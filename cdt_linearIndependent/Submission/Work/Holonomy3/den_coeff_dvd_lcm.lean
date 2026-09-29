import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.den_dvd_iff_mul_castInt

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-- Monotonicity of `lcmUpto`. -/
theorem lcmUpto_dvd_lcmUpto_of_le {M N : ℕ} (h : M ≤ N) : lcmUpto M ∣ lcmUpto N := by
  unfold Submission.CDTPlan.lcmUpto
  exact Finset.lcm_mono (fun a ha => by
    simp only [Finset.mem_Icc] at ha ⊢
    exact ⟨ha.1, le_trans ha.2 h⟩)

/-- Sharp denominator bound for the `N`-th coefficient of a single species of a family with
denominator types `K_i·n^{e_i}·∏_h [1,…,b_{i,h}·n+c_i]`: the denominator divides
`Nc·Kmax·(max 1 N)^{e_i}·∏_h [1,…,b_{i,h}·N+c]`, with `Kmax` a common multiple of the `K_i`,
`c ≥ c_i` a common shift and `Nc` a common multiple of the constant-coefficient denominators. -/
theorem den_coeff_dvd_lcm {m r : ℕ} (b : Fin m → Fin r → ℕ) (e : Fin m → ℕ)
    (f : Fin m → PowerSeries ℚ) (hden : ∀ i, Submission.CDTPlan.HasDenomType (e i) (b i) (f i))
    (Kmax c Nc : ℕ) (hK : ∀ i, (hden i).choose ∣ Kmax)
    (hc : ∀ i, (hden i).choose_spec.choose ≤ c)
    (hNc : ∀ i, (PowerSeries.coeff 0 (f i)).den ∣ Nc) :
    ∀ (a : Fin m) (N : ℕ), (PowerSeries.coeff N (f a)).den ∣
      Nc * Kmax * (max 1 N) ^ (e a) * ∏ h : Fin r, Submission.CDTPlan.lcmUpto (b a h * N + c) := by
  intro a N
  rcases eq_or_ne N 0 with rfl | hN
  · -- the constant coefficient is handled by `Nc`
    obtain ⟨k, hk⟩ := hNc a
    refine ⟨k * (Kmax * (max 1 0) ^ (e a) * ∏ h : Fin r, lcmUpto (b a h * 0 + c)), ?_⟩
    rw [hk]
    ring
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    obtain ⟨z, hz⟩ := (hden a).choose_spec.choose_spec.2 N hN1
    -- the clearing factor attached to the denominator type of species `a`
    have hDq : (((hden a).choose * N ^ (e a) *
        ∏ h : Fin r, lcmUpto (b a h * N + (hden a).choose_spec.choose) : ℕ) : ℚ) *
          PowerSeries.coeff N (f a) = (z : ℚ) := by
      push_cast
      exact hz
    have hdenD : (PowerSeries.coeff N (f a)).den ∣
        ((hden a).choose * N ^ (e a) *
          ∏ h : Fin r, lcmUpto (b a h * N + (hden a).choose_spec.choose)) :=
      den_dvd_iff_mul_castInt.mpr ⟨z, hDq⟩
    -- divide this clearing factor into the target
    have hDvd : ((hden a).choose * N ^ (e a) *
          ∏ h : Fin r, lcmUpto (b a h * N + (hden a).choose_spec.choose)) ∣
        Kmax * (max 1 N) ^ (e a) * ∏ h : Fin r, lcmUpto (b a h * N + c) := by
      refine Nat.mul_dvd_mul (Nat.mul_dvd_mul (hK a) ?_) ?_
      · simp [max_eq_right hN1]
      · refine Finset.prod_dvd_prod_of_dvd _ _ (fun h _ => ?_)
        refine lcmUpto_dvd_lcmUpto_of_le ?_
        have := hc a
        omega
    refine hdenD.trans ?_
    have hT : Nc * Kmax * (max 1 N) ^ (e a) * ∏ h : Fin r, lcmUpto (b a h * N + c)
        = Nc * (Kmax * (max 1 N) ^ (e a) * ∏ h : Fin r, lcmUpto (b a h * N + c)) := by
      ring
    rw [hT]
    obtain ⟨w, hw⟩ := hDvd
    exact ⟨w * Nc, by rw [hw]; ring⟩

end Work.Holonomy3
