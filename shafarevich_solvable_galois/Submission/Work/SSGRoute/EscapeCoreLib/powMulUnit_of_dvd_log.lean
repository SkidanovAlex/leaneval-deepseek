import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.exists_pow_mul_mem_localUnits_of_dvd_log
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.EscapeCoreLib

theorem powMulUnit_of_dvd_log {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p : ℕ) (hp : p.Prime) (β : Kˣ)
    (h : (p : ℤ) ∣ (𝔭.valuation K (β : K)).log) :
    ∃ c : K, ∃ u : Kˣ, (β : K) = c ^ p * (u : K) ∧ 𝔭.valuation K (u : K) = 1 := by
  classical
  -- Primality of `p` is irrelevant here; only `(p : ℤ) ∣ c` is used.
  have _ : p ≠ 0 := hp.ne_zero
  -- Write the `𝔭`-adic exponent `c` of `β` as `c = p * m`.
  obtain ⟨m, hm⟩ := h
  -- Surjectivity of the height-one valuation: pick `γ₀ ∈ K` with `v_𝔭 γ₀ = WithZero.exp m`.
  obtain ⟨γ₀, hγ₀⟩ :=
    IsDedekindDomain.HeightOneSpectrum.valuation_surjective K 𝔭 (WithZero.exp m)
  have hγ₀ne : γ₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hγ₀
    exact (WithZero.exp_ne_zero (a := m)) hγ₀.symm
  have hβne : (β : K) ≠ 0 := Units.ne_zero β
  -- The correction factor `u₀ = β / γ₀ ^ p`, which will be a `𝔭`-unit.
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
  refine ⟨γ₀, Units.mk0 u₀ hu₀ne, ?_, ?_⟩
  · -- `β = γ₀ ^ p * u₀` in `K`.
    show (β : K) = γ₀ ^ p * (Units.mk0 u₀ hu₀ne : K)
    rw [Units.val_mk0, hu₀, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero p hγ₀ne), mul_one]
  · -- `u₀` is a local unit at `𝔭`.
    rw [Units.val_mk0, hval]

end Work.SSGRoute.EscapeCoreLib
