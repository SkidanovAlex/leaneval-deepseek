import Mathlib
import Submission.Work.DSMap.Mix2

namespace Work.DSM5b

universe a

/-- The kernel of the localisation restriction `W_{t_S} → W_{t_T}` (`S ⊆ T`) is killed by a
power of `t_T`: if `locRes t h x = 0` then `t_T ^ n * x = 0` in `W_{t_S}` for some `n`.

Indeed `t_S ∣ t_T`, so `W_{t_T} = W[(t_T)^{-1}]` is obtained from `W_{t_S}` by inverting the image
of `t_T`; the claim is the standard "`x / s = 0` in a localisation implies `m x = 0`" statement,
with `t_S` already a unit in `W_{t_S}`. -/
theorem locRes_eq_zero_imp_pow_mul_eq_zero {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι]
    (t : ι → W) {S T : Finset ι} (h : S ⊆ T) (x : Localization.Away (DSMap.Mix2.tS t S))
    (hx : DSMap.Mix2.locRes t h x = 0) :
    ∃ n : ℕ, algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) ((DSMap.Mix2.tS t T) ^ n) * x = 0 := by
  -- write `x` as a fraction over a power of `t_S`: `x * t_S ^ k = a`
  obtain ⟨a, k, hsec⟩ : ∃ (a : W) (k : ℕ),
      x * algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) ((DSMap.Mix2.tS t S) ^ k) =
        algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) a :=
    ⟨_, _, IsLocalization.Away.sec_spec _ x⟩
  -- applying `locRes` and using `hx` shows the numerator maps to `0`
  have hmap := congrArg (DSMap.Mix2.locRes t h) hsec
  simp only [map_mul, AlgHom.commutes] at hmap
  have hz : algebraMap W (Localization.Away (DSMap.Mix2.tS t T)) a = 0 := by
    rw [← hmap, hx, zero_mul]
  -- hence some power of `t_T` annihilates `a` in `W`
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (DSMap.Mix2.tS t T))
      (Localization.Away (DSMap.Mix2.tS t T)) a).mp hz
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff m.1 (DSMap.Mix2.tS t T)).mp m.2
  rw [← hn] at hm
  refine ⟨n, ?_⟩
  -- `t_T ^ n * x` is killed by the unit `t_S ^ k`, so it vanishes
  have key : algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) ((DSMap.Mix2.tS t T) ^ n) * x *
      algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) ((DSMap.Mix2.tS t S) ^ k) = 0 := by
    rw [mul_assoc, hsec, ← map_mul, hm, map_zero]
  have hunit : IsUnit (algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) ((DSMap.Mix2.tS t S) ^ k)) := by
    simpa using IsLocalization.Away.algebraMap_pow_isUnit (DSMap.Mix2.tS t S) k
  exact (IsUnit.mul_left_eq_zero hunit).mp key

end Work.DSM5b
