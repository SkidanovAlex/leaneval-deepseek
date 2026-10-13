import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2b.assembly_aux

namespace Work.DSG4b.KerTensor

universe u

/-- **Elementwise Artin–Rees (general ideal).** Let `R` be a Noetherian ring, `I ⊆ R` an ideal and
`g : R^k → R^m` a linear map of coordinate modules. There is a constant `c` such that every
`x : R^k` whose image `g x` has all coordinates in `I ^ n` differs from an element of
`I ^ (n - c) • ⊤` by an element of `ker g`, i.e. `x ∈ ker g + I ^ (n - c) R^k`.

This is `Work.DSM2b.exists_pow_sub_mem_ker_aux` with the principal ideal `(π)` replaced by an
arbitrary ideal `I` (and the correction `π ^ (n-c) • z` by membership in `I ^ (n-c) • ⊤`). Proof:
from `Ideal.exists_pow_inf_eq_pow_smul` applied to `M = R^m` and the submodule `LinearMap.range g`
one gets `(I ^ n • ⊤) ⊓ range g ≤ I ^ (n - c) • (range g)`; use
`Work.DSM2b.mem_smul_top_fin_iff` to convert the coordinatewise hypothesis into membership in
`I ^ n • ⊤`, then spread the resulting scalar combination over a preimage. -/
theorem elementwise_artin_rees {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) :
    ∃ c : ℕ, ∀ n (x : Fin k → R), (∀ i, g x i ∈ I ^ n) →
      ∃ z ∈ I ^ (n - c) • (⊤ : Submodule R (Fin k → R)), x - z ∈ LinearMap.ker g := by
  classical
  -- Artin–Rees for the ideal `I` and the (finitely generated) submodule `range g ⊆ R^m`.
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := Fin m → R) I (LinearMap.range g)
  refine ⟨c, fun n x hx => ?_⟩
  by_cases hn : c ≤ n
  · -- Coordinatewise membership of `g x` in `I^n` upgrades to `g x ∈ I^n • ⊤`.
    have hgx : g x ∈ I ^ n • (⊤ : Submodule R (Fin m → R)) :=
      (Work.DSM2b.mem_smul_top_fin_iff (I ^ n) (g x)).mpr hx
    have h1 : g x ∈ I ^ n • (⊤ : Submodule R (Fin m → R)) ⊓ LinearMap.range g := ⟨hgx, x, rfl⟩
    -- Artin–Rees: `I^n • ⊤ ⊓ range g = I^(n-c) • (I^c • ⊤ ⊓ range g) ≤ I^(n-c) • range g`.
    rw [hc n hn] at h1
    have h2 : g x ∈ I ^ (n - c) • LinearMap.range g :=
      Submodule.smul_le.mpr (fun r hr w hw => Submodule.smul_mem_smul hr (Submodule.mem_inf.mp hw).2) h1
    -- Spread the scalar combination over a preimage: `I^(n-c) • range g ⊆ g '' (I^(n-c) • ⊤)`.
    have hle : I ^ (n - c) • LinearMap.range g ≤
        Submodule.map g (I ^ (n - c) • (⊤ : Submodule R (Fin k → R))) :=
      Submodule.smul_le.mpr (fun a ha w hw => by
        obtain ⟨z₀, rfl⟩ := hw
        exact ⟨a • z₀, Submodule.smul_mem_smul ha Submodule.mem_top, by simp⟩)
    obtain ⟨z, hzP, hzg⟩ := Submodule.mem_map.mp (hle h2)
    exact ⟨z, hzP, by rw [LinearMap.mem_ker, map_sub, hzg, sub_self]⟩
  · -- `n < c`: then `n - c = 0` and `I ^ 0 • ⊤ = ⊤`, so `z := x` works.
    rw [not_le] at hn
    refine ⟨x, ?_, ?_⟩
    · rw [Nat.sub_eq_zero_of_le (le_of_lt hn)]
      rw [show I ^ 0 = ⊤ by simp, Submodule.top_smul]
      exact Submodule.mem_top
    · rw [sub_self]; exact Submodule.zero_mem _

end Work.DSG4b.KerTensor
