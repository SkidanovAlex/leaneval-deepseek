import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.P2Close.residueInvolution
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.PlaceValBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise NumberField
open IsDedekindDomain

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute.P2Close

/-- The finite-field input `hFF` applied to the residue field `𝓞 K ⧸ 𝔭`.

The `Field` and `Fintype` instances of the quotient are supplied explicitly here (they are not
global instances), which is why this is a separate step. -/
lemma unitSquare_hFF_apply {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [NumberField ↥K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (σbar : (𝓞 ↥K ⧸ 𝔭.asIdeal) ≃+* (𝓞 ↥K ⧸ 𝔭.asIdeal))
    (hσbar2 : σbar ^ 2 = 1) (hσbar1 : σbar ≠ 1)
    (hchar : ringChar (𝓞 ↥K ⧸ 𝔭.asIdeal) ≠ 2)
    (hFF : ∀ (E : Type) [Field E] [Fintype E] (σ : E ≃+* E), σ ^ 2 = 1 → σ ≠ 1 →
      ringChar E ≠ 2 → (∀ y : E, σ y = y → IsSquare y) ∧ (∀ y : E, y * σ y = 1 → IsSquare y)) :
    (∀ y : 𝓞 ↥K ⧸ 𝔭.asIdeal, σbar y = y → IsSquare y) ∧
      (∀ y : 𝓞 ↥K ⧸ 𝔭.asIdeal, y * σbar y = 1 → IsSquare y) := by
  haveI : Finite (𝓞 ↥K ⧸ 𝔭.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI : Field (𝓞 ↥K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
  letI : Fintype (𝓞 ↥K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  exact hFF _ σbar hσbar2 hσbar1 hchar

/-- **The residue class of a unit at `𝔭` which is `ρ`-invariant or `ρ`-anti-invariant is a square
in `𝓞 K ⧸ 𝔭`**, together with a lift `r` of that class congruent to `x` at `𝔭`. -/
lemma unitSquare_residue_square {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A)
    (hnontriv : ∃ x₀ : NumberField.RingOfIntegers ↥K,
      ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ (x₀ : ↥K) - (x₀ : ↥K)) < 1))
    (hFF : ∀ (E : Type) [Field E] [Fintype E] (σ : E ≃+* E), σ ^ 2 = 1 → σ ≠ 1 →
      ringChar E ≠ 2 → (∀ y : E, σ y = y → IsSquare y) ∧ (∀ y : E, y * σ y = 1 → IsSquare y))
    (x : (↥K)ˣ) (hunit : A.valuation (algebraMap ↥K Ω (x : ↥K)) = 1)
    (hconj : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) x = x ∨
      Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) x = x⁻¹) :
    ∃ r : NumberField.RingOfIntegers ↥K,
      IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 ((x : ↥K) - (r : ↥K)) < 1 ∧
      IsSquare (Ideal.Quotient.mk 𝔭.asIdeal r) := by
  classical
  obtain ⟨σbar, hσbar_mk, hσbar2, hσbar1⟩ :=
    residueInvolution ρ hρ2 A hA 𝔭 h𝔭 hfixA hnontriv
  -- `2` is nonzero in the residue field (the place is odd)
  have h2val : ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (2 : ↥K)) < 1 := by
    intro h
    exact h2 (by
      rw [← map_ofNat (algebraMap ↥K Ω) 2]
      exact (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_lt_one_iff A 𝔭 h𝔭 (2 : ↥K)).mpr h)
  have htwo_ne : (2 : 𝓞 ↥K ⧸ 𝔭.asIdeal) ≠ 0 := by
    have hcast : ((2 : 𝓞 ↥K) : ↥K) = (2 : ↥K) := by
      first
        | rfl
        | exact map_ofNat (algebraMap (𝓞 ↥K) ↥K) 2
        | (rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_ofNat]; rfl)
        | (push_cast; ring)
        | (norm_num)
    have h2mem : ¬ (2 : 𝓞 ↥K) ∈ 𝔭.asIdeal := by
      intro hmem
      refine h2val ?_
      have h := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭
        (2 : 𝓞 ↥K)).mpr hmem
      first
        | (simpa using h)
        | (simpa only [hcast] using h)
        | (rwa [hcast] at h)
        | (exact h.trans_le (le_of_eq hcast))
    intro hzero
    have hzero' : Ideal.Quotient.mk 𝔭.asIdeal (2 : 𝓞 ↥K) = 0 := by
      first
        | (rw [map_ofNat (Ideal.Quotient.mk 𝔭.asIdeal) 2]; exact hzero)
        | (rw [show (2 : 𝓞 ↥K ⧸ 𝔭.asIdeal) =
              Ideal.Quotient.mk 𝔭.asIdeal (2 : 𝓞 ↥K) from by
                first | (rw [map_ofNat]) | rfl] at hzero
           exact hzero)
    exact h2mem (Ideal.Quotient.eq_zero_iff_mem.mp hzero')
  have hchar : ringChar (𝓞 ↥K ⧸ 𝔭.asIdeal) ≠ 2 := by
    intro hc
    haveI : CharP (𝓞 ↥K ⧸ 𝔭.asIdeal) 2 := ringChar.of_eq hc
    exact htwo_ne (CharP.cast_eq_zero _ 2)
  obtain ⟨hFFfix, hFFanti⟩ := unitSquare_hFF_apply 𝔭 σbar hσbar2 hσbar1 hchar hFF
  -- write `x = n / s` with `s` a unit at `𝔭`
  have hxle : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K) ≤ 1 :=
    (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_le_one_iff A 𝔭 h𝔭 (x : ↥K)).mp
      (le_of_eq hunit)
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (K := ↥K) 𝔭 (x : ↥K)
      hxle
  set s : 𝓞 ↥K := (d : 𝓞 ↥K) with hs_def
  have hs_notMem : s ∉ 𝔭.asIdeal := by
    rw [hs_def]
    exact Ideal.mem_primeCompl_iff.mp d.2
  have hndK : (x : ↥K) * (s : ↥K) = (n : ↥K) := by
    simpa [hs_def] using hnd
  -- the class of `s` is nonzero, so it has an inverse in the residue field, lifted to `𝓞 K`
  have hs_ne : Ideal.Quotient.mk 𝔭.asIdeal s ≠ 0 := by
    intro h
    exact hs_notMem (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := 𝔭.asIdeal)
    (a := Ideal.Quotient.mk 𝔭.asIdeal s) hs_ne
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective b
  have hts : Ideal.Quotient.mk 𝔭.asIdeal t * Ideal.Quotient.mk 𝔭.asIdeal s = 1 := by
    rw [ht, mul_comm]
    exact hb
  have hst' : Ideal.Quotient.mk 𝔭.asIdeal s * Ideal.Quotient.mk 𝔭.asIdeal t = 1 := by
    rw [mul_comm, hts]
  set r : 𝓞 ↥K := n * t with hr_def
  have hrn : Ideal.Quotient.mk 𝔭.asIdeal r =
      Ideal.Quotient.mk 𝔭.asIdeal n * Ideal.Quotient.mk 𝔭.asIdeal t := by
    rw [hr_def, map_mul]
  have hrs : Ideal.Quotient.mk 𝔭.asIdeal r * Ideal.Quotient.mk 𝔭.asIdeal s =
      Ideal.Quotient.mk 𝔭.asIdeal n := by
    rw [hrn, mul_assoc, hts, mul_one]
  -- the action of `ρ` on `x`
  have hrho : ρ (x : ↥K) = (x : ↥K) ∨ ρ (x : ↥K) = ((x : ↥K))⁻¹ := by
    have hconj'' : Units.map ρ.toMonoidHom x = x ∨ Units.map ρ.toMonoidHom x = x⁻¹ := by
      have hmap : Units.map
            (AlgEquiv.restrictNormalHom K (Work.SSGRoute.ZDataMup.galLift K ρ)).toMonoidHom x =
          Units.map ρ.toMonoidHom x := by
        rw [Work.SSGRoute.ZDataMup.galLift_spec K ρ]
      rcases hconj with h | h
      · left
        unfold Work.SSGRoute.H9.conjUnit at h
        rwa [hmap] at h
      · right
        unfold Work.SSGRoute.H9.conjUnit at h
        rwa [hmap] at h
    rcases hconj'' with h | h
    · left
      have h' := congrArg (fun u : (↥K)ˣ => (u : ↥K)) h
      simpa [Units.coe_map] using h'
    · right
      have h' := congrArg (fun u : (↥K)ˣ => (u : ↥K)) h
      simpa [Units.coe_map] using h'
  -- the two algebraic relations between `n` and `s` coming from the invariance of `x`
  have hrel_inv_K : ρ (x : ↥K) = (x : ↥K) →
      ρ (n : ↥K) * (s : ↥K) = (n : ↥K) * ρ (s : ↥K) := by
    intro hx
    have hm : ρ (n : ↥K) = ρ (x : ↥K) * ρ (s : ↥K) := by rw [← hndK, map_mul]
    rw [hm, hx]
    linear_combination (ρ (s : ↥K)) * hndK
  have hrel_anti_K : ρ (x : ↥K) = ((x : ↥K))⁻¹ →
      ρ (n : ↥K) * (n : ↥K) = ρ (s : ↥K) * (s : ↥K) := by
    intro hx
    have hm : ρ (n : ↥K) = ρ (x : ↥K) * ρ (s : ↥K) := by rw [← hndK, map_mul]
    have hxx : ρ (x : ↥K) * (x : ↥K) = 1 := by
      rw [hx, inv_mul_cancel₀ (Units.ne_zero x)]
    have hndK' : (n : ↥K) = (x : ↥K) * (s : ↥K) := hndK.symm
    rw [hm]
    linear_combination (ρ (x : ↥K) * ρ (s : ↥K)) * hndK' +
      (ρ (s : ↥K) * (s : ↥K)) * hxx
  have hn : (algebraMap (𝓞 ↥K) ↥K) (ρ • n : 𝓞 ↥K) = ρ (n : ↥K) :=
    integralClosure.coe_smul ρ n
  have hs : (algebraMap (𝓞 ↥K) ↥K) (ρ • s : 𝓞 ↥K) = ρ (s : ↥K) :=
    integralClosure.coe_smul ρ s
  have hrel_inv : ρ (x : ↥K) = (x : ↥K) →
      (ρ • n : 𝓞 ↥K) * s = n * (ρ • s : 𝓞 ↥K) := by
    intro hx
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_mul, map_mul, hn, hs]
    exact hrel_inv_K hx
  have hrel_anti : ρ (x : ↥K) = ((x : ↥K))⁻¹ →
      (ρ • n : 𝓞 ↥K) * n = (ρ • s : 𝓞 ↥K) * s := by
    intro hx
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_mul, map_mul, hn, hs]
    exact hrel_anti_K hx
  -- `mk (ρ • s)` is nonzero because `σbar` is injective
  have hρs_ne : Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) ≠ 0 := by
    rw [← hσbar_mk s]
    exact fun h => hs_ne (σbar.injective (by rw [h, map_zero]))
  refine ⟨r, ?_, ?_⟩
  · -- the congruence `x ≡ r (mod 𝔭)`
    have hst : Ideal.Quotient.mk 𝔭.asIdeal (s * t) = 1 := by
      rw [map_mul, mul_comm, hts]
    have hmem : (s * t - 1 : 𝓞 ↥K) ∈ 𝔭.asIdeal := by
      have h0 : Ideal.Quotient.mk 𝔭.asIdeal (s * t - 1) = 0 := by
        rw [map_sub, hst, map_one, sub_self]
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    have hcoe1 : (algebraMap (𝓞 ↥K) ↥K) (s * t - 1) = (s : ↥K) * (t : ↥K) - 1 := by
      rw [map_sub, map_mul, map_one]
    have hlt : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭
        ((s : ↥K) * (t : ↥K) - 1) < 1 := by
      have h2 := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭
        (s * t - 1)).mpr hmem
      first
        | (simpa only [hcoe1] using h2)
        | (simpa using h2)
        | (convert h2 using 1; push_cast; ring)
    have hlt' : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭
        (1 - (s : ↥K) * (t : ↥K)) < 1 := by
      have hneg : (1 : ↥K) - (s : ↥K) * (t : ↥K) = -((s : ↥K) * (t : ↥K) - 1) := by ring
      rw [hneg, Valuation.map_neg]
      exact hlt
    have hr1 : ((r : 𝓞 ↥K) : ↥K) = (n : ↥K) * (t : ↥K) := by
      rw [hr_def]
      rfl
    have hr' : ((r : 𝓞 ↥K) : ↥K) = (x : ↥K) * (s : ↥K) * (t : ↥K) := by
      rw [hr1, ← hndK]
    have hprod : (x : ↥K) - (r : ↥K) = (x : ↥K) * (1 - (s : ↥K) * (t : ↥K)) := by
      rw [hr']
      ring
    rw [hprod, map_mul]
    calc IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K) *
            IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (1 - (s : ↥K) * (t : ↥K))
        = IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (1 - (s : ↥K) * (t : ↥K)) *
            IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K) := mul_comm _ _
      _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (1 - (s : ↥K) * (t : ↥K)) * 1 :=
          mul_le_mul_right hxle _
      _ = IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (1 - (s : ↥K) * (t : ↥K)) :=
          mul_one _
      _ < 1 := hlt'
  · rcases hrho with hx | hx
    · -- invariant case: `σbar` fixes the class of `r`
      refine hFFfix (Ideal.Quotient.mk 𝔭.asIdeal r) ?_
      have hmkeq : Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) * Ideal.Quotient.mk 𝔭.asIdeal s =
          Ideal.Quotient.mk 𝔭.asIdeal n * Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by
        rw [← map_mul, ← map_mul, hrel_inv hx]
      have h1 : σbar (Ideal.Quotient.mk 𝔭.asIdeal r) * Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) =
          Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) := by
        rw [← hσbar_mk s, ← hσbar_mk n, ← map_mul, hrs]
      have h3 : (σbar (Ideal.Quotient.mk 𝔭.asIdeal r) * Ideal.Quotient.mk 𝔭.asIdeal s) *
            Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) =
          Ideal.Quotient.mk 𝔭.asIdeal n * Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by
        rw [mul_assoc, mul_comm (Ideal.Quotient.mk 𝔭.asIdeal s), ← mul_assoc, h1, hmkeq]
      have h4 : σbar (Ideal.Quotient.mk 𝔭.asIdeal r) * Ideal.Quotient.mk 𝔭.asIdeal s =
          Ideal.Quotient.mk 𝔭.asIdeal n := mul_right_cancel₀ hρs_ne h3
      exact mul_right_cancel₀ hs_ne (by rw [h4, hrs])
    · -- anti-invariant case: the class of `r` has norm one
      refine hFFanti (Ideal.Quotient.mk 𝔭.asIdeal r) ?_
      have hmkeq : Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) * Ideal.Quotient.mk 𝔭.asIdeal n =
          Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) * Ideal.Quotient.mk 𝔭.asIdeal s := by
        rw [← map_mul, ← map_mul, hrel_anti hx]
      have h1 : σbar (Ideal.Quotient.mk 𝔭.asIdeal r) * Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) =
          Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) := by
        rw [← hσbar_mk s, ← hσbar_mk n, ← map_mul, hrs]
      have h6 : Ideal.Quotient.mk 𝔭.asIdeal r * Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) =
          Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by
        rw [hrn]
        calc (Ideal.Quotient.mk 𝔭.asIdeal n * Ideal.Quotient.mk 𝔭.asIdeal t) *
              Ideal.Quotient.mk 𝔭.asIdeal (ρ • n)
            = Ideal.Quotient.mk 𝔭.asIdeal (ρ • n) * Ideal.Quotient.mk 𝔭.asIdeal n *
                Ideal.Quotient.mk 𝔭.asIdeal t := by ring
          _ = Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) * Ideal.Quotient.mk 𝔭.asIdeal s *
                Ideal.Quotient.mk 𝔭.asIdeal t := by rw [hmkeq]
          _ = Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by rw [mul_assoc, hst', mul_one]
      have h7 : Ideal.Quotient.mk 𝔭.asIdeal r * σbar (Ideal.Quotient.mk 𝔭.asIdeal r) *
            Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) = Ideal.Quotient.mk 𝔭.asIdeal (ρ • s) := by
        rw [mul_assoc, h1, h6]
      exact mul_right_cancel₀ hρs_ne (by rw [h7, one_mul])

/-- **The unit case of the "inert squareness" of Schmidt--Wingberg p. 16.**

`k` a number field, `Ω` an algebraic closure, `K` a finite Galois intermediate field, `A` a finite
place of `Ω` over `k` with `𝔭` the prime of `𝓞 K` below it and `¬ A.valuation (2 : Ω) < 1` (so `A`
is odd), and `ρ ∈ Gal(K|k)` an **involution** (`ρ ^ 2 = 1`, `ρ ≠ 1` in the application).  Assume
the lift `σ = galLift K ρ` fixes `A`, that an `x₀ : 𝓞 K` exists with
`𝔭.valuation (ρ x₀ - x₀) ≮ 1`, i.e. the induced action of `ρ` on the residue field
`κ = 𝓞 K ⧸ 𝔭` is nontrivial (a *hypothesis* here; it is proved separately from `hunram`), and the
finite-field input `hFF` (a finite field of odd characteristic with a nontrivial involution has all
fixed elements and all norm-one elements square; see `SSGRoute/P2Close/involutionIsSquare`).

Then for every `x ∈ Kˣ` which is a **unit at `A`** (`A.valuation (algebraMap x) = 1`) and is either
invariant (`conjUnit (galLift K ρ) x = x`) or anti-invariant
(`conjUnit (galLift K ρ) x = x⁻¹`), the image of `x` in the `𝔭`-adic completion `K_𝔭` is a square.

Mathematical content.  `ρ` preserves `𝔭` (from `hfixA` and the `< 1`-transport
`Work.SSGRoute.smul_valuation_lt_one`), hence induces an involution `σ_κ` on `κ = 𝓞 K ⧸ 𝔭` with
`σ_κ ≠ 1` (the nontriviality hypothesis) and `σ_κ² = 1` (from `hρ2`).  `x` is a unit at `A`, so
`𝔭.valuation` on `x` and on `x⁻¹` is `≤ 1` (bridge `A.valuation (algebraMap y) < 1 ↔ 𝔭.valuation y < 1`
for `y = x, x⁻¹`, e.g. `Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_lt_one_iff`), and
`IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer` writes `x = n / s` with
`n, s : 𝓞 K`, `s ∉ 𝔭`; the class `r = (n mod 𝔭) * (s mod 𝔭)⁻¹ ∈ κ^×` is then defined, and
invariance of `x` gives `σ_κ r = r` while anti-invariance gives `r * σ_κ r = 1`.  By `hFF`, `r` is
a square in `κ`; the ring isomorphism of
`Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv 𝔭 1` (the `n = 1`
instance; it is compatible with `algebraMap` and `Ideal.Quotient.mk`) transports this to the
squareness of the residue of the image of `x` in
`IsLocalRing.ResidueField (𝔭.adicCompletionIntegers ↥K)`.  Since `2` is a unit of
`𝔭.adicCompletionIntegers ↥K` (from `h2`, e.g. via
`Work.SSGRoute.ZDataTwo.isUnit_two_adicCompletionIntegers_of_not_lt_one`), Hensel's lemma
`Work.SSGRoute.NodeS37.exists_sq_of_residue_isSquare` produces the square root in the completion.

Note: `Submission.NK.*` and `Submission.Commons.*` modules are importable from a module under
`Submission/Work/` (see e.g. `Submission/Work/SSGRoute/inertiaAtLevelDefs.lean`). -/
theorem unitSquare {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A)
    (hnontriv : ∃ x₀ : NumberField.RingOfIntegers ↥K,
      ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ (x₀ : ↥K) - (x₀ : ↥K)) < 1))
    (hFF : ∀ (E : Type) [Field E] [Fintype E] (σ : E ≃+* E), σ ^ 2 = 1 → σ ≠ 1 →
      ringChar E ≠ 2 → (∀ y : E, σ y = y → IsSquare y) ∧ (∀ y : E, y * σ y = 1 → IsSquare y))
    (x : (↥K)ˣ) (hunit : A.valuation (algebraMap ↥K Ω (x : ↥K)) = 1)
    (hconj : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) x = x ∨
      Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) x = x⁻¹) :
    ∃ c : (𝔭.adicCompletion ↥K)ˣ,
      Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom x = c ^ 2 := by
  classical
  obtain ⟨r, hrval, hrsq⟩ :=
    unitSquare_residue_square ρ hρ2 A hA 𝔭 h𝔭 h2 hfixA hnontriv hFF x hunit hconj
  -- `2` is a unit of the integers of the completion
  have h2val : ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (2 : ↥K)) < 1 := by
    intro h
    exact h2 (by
      rw [← map_ofNat (algebraMap ↥K Ω) 2]
      exact (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_lt_one_iff A 𝔭 h𝔭 (2 : ↥K)).mpr h)
  have h2unit : IsUnit (2 : 𝔭.adicCompletionIntegers ↥K) :=
    Work.SSGRoute.ZDataTwo.TwoRec.isUnit_two_adicCompletionIntegers_of_not_lt_one 𝔭 h2val
  -- the image of `x` in the completion is a unit of the integer ring
  have hcoe : ∀ y : ↥K, Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) y) =
      IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 y := fun y =>
    Work.SSGRoute.NodeS37.valued_adicCompletion_eq 𝔭 y
  have hxle : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K) ≤ 1 :=
    (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_le_one_iff A 𝔭 h𝔭 (x : ↥K)).mp
      (le_of_eq hunit)
  have hmem : algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K) ∈ 𝔭.adicCompletionIntegers ↥K := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    simp only [hcoe]
    exact hxle
  have hxnotlt : ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (x : ↥K)) < 1 := by
    intro h
    have h' := (Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_lt_one_iff A 𝔭 h𝔭 (x : ↥K)).mpr h
    rw [hunit] at h'
    exact lt_irrefl 1 h'
  have hxnotlt' : ¬ (Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K)) < 1) := by
    simp only [hcoe]
    exact hxnotlt
  have hu : IsUnit (⟨algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K), hmem⟩ :
      𝔭.adicCompletionIntegers ↥K) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem2
    refine hxnotlt' ?_
    have h :=
      (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        𝔭 (⟨algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K), hmem⟩ :
          𝔭.adicCompletionIntegers ↥K)).mp hmem2
    simpa using h
  have hux : algebraMap (𝔭.adicCompletionIntegers ↥K) (𝔭.adicCompletion ↥K)
      (hu.unit : 𝔭.adicCompletionIntegers ↥K) =
      algebraMap ↥K (𝔭.adicCompletion ↥K) (x : ↥K) := by
    simp [IsUnit.unit_spec]
  -- the difference `u - r` is in the maximal ideal
  have hr_mem : (hu.unit : 𝔭.adicCompletionIntegers ↥K) -
      algebraMap (𝓞 ↥K) (𝔭.adicCompletionIntegers ↥K) r ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ↥K) := by
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
      𝔭]
    change Valued.v (algebraMap (𝔭.adicCompletionIntegers ↥K) (𝔭.adicCompletion ↥K)
      ((hu.unit : 𝔭.adicCompletionIntegers ↥K) -
        algebraMap (𝓞 ↥K) (𝔭.adicCompletionIntegers ↥K) r)) < 1
    rw [map_sub, hux]
    have htower : ((algebraMap (𝓞 ↥K) (𝔭.adicCompletionIntegers ↥K) r :
          𝔭.adicCompletionIntegers ↥K) : 𝔭.adicCompletion ↥K) =
        algebraMap ↥K (𝔭.adicCompletion ↥K) (r : ↥K) := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply (R := 𝓞 ↥K)
        (K := ↥K) 𝔭 r]
      exact IsScalarTower.algebraMap_apply (𝓞 ↥K) ↥K (𝔭.adicCompletion ↥K) r
    rw [show algebraMap (𝔭.adicCompletionIntegers ↥K) (𝔭.adicCompletion ↥K)
          (algebraMap (𝓞 ↥K) (𝔭.adicCompletionIntegers ↥K) r) =
          algebraMap ↥K (𝔭.adicCompletion ↥K) (r : ↥K) from htower]
    rw [← map_sub]
    simp only [hcoe]
    exact hrval
  have hsq_res : IsSquare ((IsLocalRing.residue (𝔭.adicCompletionIntegers ↥K))
      (hu.unit : 𝔭.adicCompletionIntegers ↥K)) :=
    Work.SSGRoute.NodeS37.isSquare_residue_of_isSquare_mk 𝔭
      (hu.unit : 𝔭.adicCompletionIntegers ↥K) r hr_mem hrsq
  obtain ⟨c, hc⟩ :=
    Work.SSGRoute.NodeS37.exists_sq_of_residue_isSquare 𝔭 h2unit hu.unit hsq_res
  refine ⟨c, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.coe_map, hc]
  exact hux.symm

end Work.SSGRoute.P2Close
