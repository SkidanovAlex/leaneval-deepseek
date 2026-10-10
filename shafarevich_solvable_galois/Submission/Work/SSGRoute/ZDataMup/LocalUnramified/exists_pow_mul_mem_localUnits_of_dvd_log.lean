import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localUnits_iff_localAlgebraMapUnits
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Splitting a `𝔭`-unit off `β` after a `p`-th power at the prime `𝔭`

Let `K` be a number field, `𝔭` a nonzero prime of `𝓞 K`, `p` a prime and `β ∈ Kˣ`.  Write
`c = log (v_𝔭 β) ∈ ℤ` for the `𝔭`-adic exponent of `β`, i.e. `v_𝔭 β = WithZero.exp c` for
Mathlib's normalisation of the height-one valuation.  If `p ∣ c`, say `c = p * m`, then `β` is a
`p`-th power **up to a local unit at `𝔭`**: there are `γ, u ∈ (K_𝔭)ˣ` with `u` a local unit
(`𝒪_𝔭ˣ`) and `β = γ ^ p * u` in the completion `K_𝔭`.

This is the "valuation divisible by `p`" half of the Kummer dictionary: it says that the Kummer
class of `β` is unramified at `𝔭` as soon as the `𝔭`-adic valuation of `β` is a `p`-th power.

## Proof

`𝔭.valuation K : K → ℤᵐ⁰` is surjective (`HeightOneSpectrum.valuation_surjective`), so choose
`γ₀ ∈ K` with `v_𝔭 γ₀ = WithZero.exp m`; then `v_𝔭 (γ₀ ^ p) = WithZero.exp (p * m) = WithZero.exp c
= v_𝔭 β`, so `u₀ = β * (γ₀ ^ p)⁻¹ ∈ K` has `v_𝔭 u₀ = 1`, i.e. is a unit at `𝔭`.  The
`p`-th power `γ` and the local unit `u` are the images of `γ₀` and `u₀` in the completion, where
`Valued.v (algebraMap K K_𝔭 x) = 𝔭.valuation K x` and `Valued.v u = 1` characterises the local
units (`Place.mem_localUnits_ofFinite_iff_valued_eq_one`).
-/

namespace Work.SSGRoute.ZDataMup.LocalUnramified

theorem exists_pow_mul_mem_localUnits_of_dvd_log
    {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p : ℕ) (hp : p.Prime) (β : Kˣ)
    (h : (p : ℤ) ∣ (𝔭.valuation K (β : K)).log) :
    ∃ (γ : (𝔭.adicCompletion K)ˣ) (u : (𝔭.adicCompletion K)ˣ),
      u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭) ∧
      Units.map (algebraMap K (𝔭.adicCompletion K)) β = γ ^ p * u := by
  classical
  -- Primality of `p` is not used in this direction; only `(p : ℤ) ∣ c` matters.
  have _ : p ≠ 0 := hp.ne_zero
  -- Write the `𝔭`-adic exponent `c` of `β` as `c = p * m`.
  obtain ⟨m, hm⟩ := h
  -- Choose `γ₀ ∈ K` with `v_𝔭 γ₀ = WithZero.exp m`.
  obtain ⟨γ₀, hγ₀⟩ :=
    IsDedekindDomain.HeightOneSpectrum.valuation_surjective K 𝔭 (WithZero.exp m)
  have hγ₀ne : γ₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hγ₀
    exact (WithZero.exp_ne_zero (a := m)) hγ₀.symm
  have hβne : (β : K) ≠ 0 := Units.ne_zero β
  -- The correction factor `u₀ = β / γ₀ ^ p`, a `𝔭`-unit.
  set u₀ : K := (β : K) * (γ₀ ^ p)⁻¹ with hu₀
  have hu₀ne : u₀ ≠ 0 := by
    rw [hu₀]
    exact mul_ne_zero hβne (inv_ne_zero (pow_ne_zero p hγ₀ne))
  have hvβ : 𝔭.valuation K (β : K) =
      WithZero.exp ((𝔭.valuation K (β : K)).log) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff (𝔭.valuation K)).mpr hβne)).symm
  -- `v_𝔭 u₀ = 1`, i.e. `u₀` is a unit at `𝔭`.
  have hval : 𝔭.valuation K u₀ = 1 := by
    rw [hu₀, map_mul, Valuation.map_inv, Valuation.map_pow, hγ₀, ← WithZero.exp_nsmul p m,
      nsmul_eq_mul, hvβ, hm]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  refine ⟨Units.map (algebraMap K (𝔭.adicCompletion K)) (Units.mk0 γ₀ hγ₀ne),
    Units.map (algebraMap K (𝔭.adicCompletion K)) (Units.mk0 u₀ hu₀ne), ?_, ?_⟩
  · -- `u₀` maps to a local unit of the completion.
    rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    show Valued.v (algebraMap K (𝔭.adicCompletion K) u₀) = 1
    rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    exact hval
  · -- The decomposition `β = γ₀ ^ p * u₀` in `Kˣ` maps to the completion.
    have hmain : β = (Units.mk0 γ₀ hγ₀ne) ^ p * Units.mk0 u₀ hu₀ne := by
      ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
      rw [mul_left_comm, mul_inv_cancel₀ (pow_ne_zero p hγ₀ne), mul_one]
    rw [hmain, map_mul, map_pow]

end Work.SSGRoute.ZDataMup.LocalUnramified
