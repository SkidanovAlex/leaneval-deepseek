import Mathlib.RingTheory.Frobenius
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.exists_frobenius_galRestrict
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
import Submission.NK.CFTLib.ARL.autToPow_eq_of_pow_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain

namespace NK.CFTLib.IdeleHasse.Descent

/-- **The reduction of a primitive `l`-th root of unity is not `1`.**  If `l` is a prime which
does not divide the residue characteristic of the place `Q` of `K`, and `w | Q` is a place of `M`
above `Q`, then a primitive `l`-th root of unity `ζ ∈ 𝓞 M` cannot reduce to `1` at `w`:
otherwise the geometric sum `∑_{i<l} ζ^i = 0` would reduce to `(l : κ_w) = 0`, forcing
`l ∈ w ∩ 𝓞 K = Q`. -/
theorem residue_mk_ne_one_of_isPrimitiveRoot {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (l : ℕ) (hl : l.Prime) (hlQ : ¬ (l : 𝓞 K) ∈ Q.asIdeal)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    (ζ : 𝓞 M) (hζ : IsPrimitiveRoot (ζ : M) l) :
    Ideal.Quotient.mk w.asIdeal ζ ≠ 1 := by
  haveI := hw
  intro h1
  have hsumM : ∑ i ∈ Finset.range l, (ζ : M) ^ i = 0 := hζ.geom_sum_eq_zero hl.one_lt
  have hsumO : ∑ i ∈ Finset.range l, ζ ^ i = 0 := by
    apply NumberField.RingOfIntegers.coe_injective (K := M)
    simpa [map_sum, map_pow] using hsumM
  have hsumκ : ∑ i ∈ Finset.range l, (Ideal.Quotient.mk w.asIdeal ζ) ^ i = 0 := by
    have h := congrArg (Ideal.Quotient.mk w.asIdeal) hsumO
    simpa [map_sum, map_pow] using h
  rw [h1] at hsumκ
  have hzero : (l : 𝓞 M ⧸ w.asIdeal) = 0 := by
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsumκ
  have hmem : (l : 𝓞 M) ∈ w.asIdeal := (Ideal.Quotient.eq_zero_iff_mem).mp hzero
  refine hlQ ?_
  rw [hw.over, Ideal.mem_under, map_natCast]
  exact hmem

theorem cyclotomicLocalDegree {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (l : ℕ) (hl : l.Prime) (hlQ : ¬ (l : NumberField.RingOfIntegers K) ∈ Q.asIdeal)
    {M : Type} [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M]
    [IsCyclotomicExtension {l} K M]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal) :
    w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
        orderOf ((Ideal.absNorm Q.asIdeal : ℕ) : ZMod l) := by
  classical
  haveI hne : NeZero l := ⟨hl.ne_zero⟩
  haveI hgal : IsGalois K M := IsCyclotomicExtension.isGalois ({l} : Set ℕ) K M
  haveI hlies : w.asIdeal.LiesOver Q.asIdeal := hw
  -- a primitive `l`-th root of unity in `𝓞 M`
  obtain ⟨ζM, hζM⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K M (Set.mem_singleton l) hl.ne_zero
  have hζint : IsIntegral ℤ ζM := hζM.isIntegral hl.pos
  let ζ : 𝓞 M := ⟨ζM, hζint⟩
  have hζcoe : (ζ : M) = ζM := rfl
  have hζ : IsPrimitiveRoot (ζ : M) l := by rw [hζcoe]; exact hζM
  have hζpow : ζ ^ l = 1 := by
    apply NumberField.RingOfIntegers.coe_injective (K := M)
    rw [map_pow, map_one]
    exact hζM.pow_eq_one
  have hlw : (l : 𝓞 M) ∉ w.asIdeal := by
    intro h
    refine hlQ ?_
    rw [hw.over, Ideal.mem_under, map_natCast]
    exact h
  -- the residue of `ζ` is a primitive `l`-th root of unity
  have hζbar_ne : Ideal.Quotient.mk w.asIdeal ζ ≠ 1 :=
    residue_mk_ne_one_of_isPrimitiveRoot Q l hl hlQ w hw ζ hζ
  have hζbar : IsPrimitiveRoot (Ideal.Quotient.mk w.asIdeal ζ) l := by
    refine IsPrimitiveRoot.iff_orderOf.mpr ?_
    have hpow1 : (Ideal.Quotient.mk w.asIdeal ζ) ^ l = 1 := by
      simpa using congrArg (Ideal.Quotient.mk w.asIdeal) hζpow
    rcases (Nat.dvd_prime hl).mp (orderOf_dvd_iff_pow_eq_one.mpr hpow1) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hζbar_ne
    · exact h
  -- ## Step 1: the inertia group at `w` is trivial, hence `e = 1`
  have hinertia : Ideal.inertia (M ≃ₐ[K] M) w.asIdeal = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    have hfix : ∀ x : 𝓞 M, σ • x - x ∈ w.asIdeal :=
      fun x => (AddSubgroup.mem_inertia.mp hσ) x
    have hsmul : σ • ζ = galRestrict (𝓞 K) K M (𝓞 M) σ ζ :=
      Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict σ ζ
    have hres : Ideal.Quotient.mk w.asIdeal (galRestrict (𝓞 K) K M (𝓞 M) σ ζ) =
        Ideal.Quotient.mk w.asIdeal ζ :=
      Ideal.Quotient.eq.mpr (by rw [← hsmul]; exact hfix ζ)
    have hspec : ζM ^ (↑(IsPrimitiveRoot.autToPow K hζM σ) : ZMod l).val = σ ζM :=
      IsPrimitiveRoot.autToPow_spec K hζM σ
    have hgal : galRestrict (𝓞 K) K M (𝓞 M) σ ζ =
        ζ ^ (↑(IsPrimitiveRoot.autToPow K hζM σ) : ZMod l).val := by
      apply NumberField.RingOfIntegers.coe_injective (K := M)
      rw [map_pow, algebraMap_galRestrict_apply (𝓞 K) σ ζ]
      show σ ζM = ζM ^ (↑(IsPrimitiveRoot.autToPow K hζM σ) : ZMod l).val
      rw [← hspec]
    have hpow : (Ideal.Quotient.mk w.asIdeal ζ) ^ (↑(IsPrimitiveRoot.autToPow K hζM σ) : ZMod l).val =
        Ideal.Quotient.mk w.asIdeal ζ := by
      rw [← map_pow, ← hgal, hres]
    have ha1 : (↑(IsPrimitiveRoot.autToPow K hζM σ) : ZMod l).val = 1 :=
      hζbar.pow_inj (ZMod.val_lt _) hl.one_lt (by rw [hpow, pow_one])
    have hσζ : σ ζM = ζM := by rw [← hspec, ha1, pow_one]
    have hunit : IsPrimitiveRoot.autToPow K hζM σ = 1 := by
      apply Units.ext
      simpa using
        NK.CFTLib.ARL.autToPow_eq_of_pow_eq hζM σ 1 (by rw [pow_one]; exact hσζ)
    have hone : IsPrimitiveRoot.autToPow K hζM (1 : M ≃ₐ[K] M) = 1 :=
      map_one (IsPrimitiveRoot.autToPow K hζM)
    exact IsPrimitiveRoot.autToPow_injective K hζM (by rw [hunit, hone])
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      Q.asIdeal w.asIdeal).mp hinertia
  -- ## Step 2: an arithmetic Frobenius at `w`
  obtain ⟨σ, hσmap, hσres⟩ :=
    Commons.NumberTheory.NumberField.exists_frobenius_galRestrict (K := K) (L := M) Q w hw
  have hσarith : IsArithFrobAt (𝓞 K) σ w.asIdeal := by
    intro x
    refine Ideal.Quotient.eq.mp ?_
    show (Ideal.Quotient.mk w.asIdeal) (σ • x) =
      (Ideal.Quotient.mk w.asIdeal) (x ^ Nat.card (𝓞 K ⧸ Ideal.under (𝓞 K) w.asIdeal))
    rw [← hw.over, map_pow,
      Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict]
    exact hσres x
  have hf : w.asIdeal.inertiaDeg (𝓞 K) = orderOf σ :=
    (Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg Q w hw he σ hσmap hσres).symm
  -- ## Step 3: the Frobenius acts on `ζM` by the norm of `Q`
  have hσζ : σ ζM = ζM ^ Nat.card (𝓞 K ⧸ Q.asIdeal) := by
    have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one
      (φ := MulSemiringAction.toAlgHom (𝓞 K) (𝓞 M) σ) hσarith hζpow hlw
    rw [← hw.over] at h
    have h2 := congrArg (algebraMap (𝓞 M) M) h
    rw [map_pow] at h2
    have h2' : (algebraMap (𝓞 M) M) (σ • ζ) =
        (algebraMap (𝓞 M) M) (ζ ^ Nat.card (𝓞 K ⧸ Q.asIdeal)) := h2
    rw [Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict,
      algebraMap_galRestrict_apply (𝓞 K) σ ζ] at h2'
    exact h2'
  have hχeq : ((↑(IsPrimitiveRoot.autToPow K hζM σ) : ZMod l)) =
      ((Nat.card (𝓞 K ⧸ Q.asIdeal) : ℕ) : ZMod l) :=
    NK.CFTLib.ARL.autToPow_eq_of_pow_eq hζM σ (Nat.card (𝓞 K ⧸ Q.asIdeal)) hσζ
  have hordχ : orderOf (IsPrimitiveRoot.autToPow K hζM σ) =
      orderOf ((Nat.card (𝓞 K ⧸ Q.asIdeal) : ℕ) : ZMod l) := by
    rw [← orderOf_units (y := IsPrimitiveRoot.autToPow K hζM σ), hχeq]
  have hordσ : orderOf σ = orderOf ((Nat.card (𝓞 K ⧸ Q.asIdeal) : ℕ) : ZMod l) := by
    rw [← orderOf_injective _ (IsPrimitiveRoot.autToPow_injective K hζM) σ]
    exact hordχ
  -- ## Step 4: conclude
  have habs : Nat.card (𝓞 K ⧸ Q.asIdeal) = Ideal.absNorm Q.asIdeal := by
    rw [Ideal.absNorm_apply]; rfl
  refine ⟨he, ?_⟩
  rw [hf, hordσ, habs]

end NK.CFTLib.IdeleHasse.Descent
