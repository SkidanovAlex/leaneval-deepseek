import Mathlib

set_option linter.style.haveILetI false

namespace Work.DSEQ0.FFR

universe u

/-- `torsionBy R M (x ^ k)` is the kernel of the `k`-th power of the linear map
`lsmul R M x`, i.e. multiplication by `x` on `M`. -/
private lemma torsionBy_pow_eq_ker_lsmul
    (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] (x : R) (k : ℕ) :
    Submodule.torsionBy R M (x ^ k) = LinearMap.ker ((LinearMap.lsmul R M x) ^ k) := by
  have hpow : ∀ k : ℕ, (LinearMap.lsmul R M x) ^ k = LinearMap.lsmul R M (x ^ k) := by
    intro k
    induction k with
    | zero => ext m; simp
    | succ k ih =>
      ext m
      simp only [pow_succ, ih, Module.End.mul_apply, LinearMap.lsmul_apply, mul_smul]
  rw [hpow k, LinearMap.lsmul_eq_distribSMulToLinearMap]
  rfl

theorem torsionBy_stabilizes (R : Type u) [CommRing R] [IsNoetherianRing R] {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R) : ∃ K : ℕ, (⨆ k : ℕ, Submodule.torsionBy R M (x ^ k)) ≤ Submodule.torsionBy R M (x ^ K) := by
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  obtain ⟨K, hK⟩ :=
    Filter.eventually_atTop.mp (LinearMap.eventually_iSup_ker_pow_eq (LinearMap.lsmul R M x))
  refine ⟨K, ?_⟩
  have hmain : (⨆ k : ℕ, Submodule.torsionBy R M (x ^ k)) = Submodule.torsionBy R M (x ^ K) := by
    rw [iSup_congr (torsionBy_pow_eq_ker_lsmul R x), hK K le_rfl, torsionBy_pow_eq_ker_lsmul R x K]
  exact hmain.le

end Work.DSEQ0.FFR
