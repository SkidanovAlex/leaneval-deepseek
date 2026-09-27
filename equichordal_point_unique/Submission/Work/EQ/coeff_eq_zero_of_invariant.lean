import Mathlib

namespace Work.EQ

/-- **Vanishing of power-series coefficients off the multiples of `k`.** Let `H` be analytic at `0`
with power series `p`, invariant near `0` under multiplication by a primitive `k`-th root of unity
`η` (`k > 0`). Then every coefficient `p.coeff n` with `k` not dividing `n` vanishes. -/
theorem coeff_eq_zero_of_invariant {H : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt H p 0) {k : ℕ} (hk : 0 < k) {η : ℂ} (hη : IsPrimitiveRoot η k)
    (hinv : ∀ᶠ z in nhds (0 : ℂ), H (η * z) = H z) {n : ℕ} (hn : ¬ k ∣ n) : p.coeff n = 0 := by
  -- `u` is the ℂ-linear map `z ↦ η * z`.
  set u : ℂ →L[ℂ] ℂ := η • ContinuousLinearMap.id ℂ ℂ with hu
  have hu_apply : ∀ z : ℂ, u z = η * z := by
    intro z
    simp [hu]
  -- The function `z ↦ H (η * z)` has power series `p.compContinuousLinearMap u` at `0`.
  have hcomp : HasFPowerSeriesAt (H ∘ u) (p.compContinuousLinearMap u) 0 := by
    have hp' : HasFPowerSeriesAt H p (u 0) := by rw [hu_apply 0, mul_zero]; exact hp
    exact hp'.compContinuousLinearMap (u := u) (x := (0 : ℂ))
  -- It agrees with `H` near `0`, so by uniqueness of power series the two series coincide.
  have hfun : ∀ᶠ z in nhds (0 : ℂ), (H ∘ u) z = H z := by
    filter_upwards [hinv] with z hz
    rw [Function.comp_apply, hu_apply z]
    exact hz
  have h_eq : p.compContinuousLinearMap u = p :=
    hcomp.eq_formalMultilinearSeries_of_eventually hp hfun
  -- The `n`-th coefficient of the composed series is `η ^ n • p.coeff n`.
  have hcomp1 : (⇑u ∘ (1 : Fin n → ℂ)) = (fun _ => η) := by
    funext i
    simp [hu_apply]
  have hcoeff : (p.compContinuousLinearMap u).coeff n = η ^ n • p.coeff n := by
    show (p.compContinuousLinearMap u) n 1 = η ^ n • p.coeff n
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply, hcomp1,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  -- Hence `p.coeff n = η ^ n • p.coeff n`, and `η ^ n ≠ 1`, so `p.coeff n = 0`.
  have hfix : p.coeff n = η ^ n • p.coeff n := by rw [← hcoeff, h_eq]
  have hne : η ^ n ≠ 1 := fun h => hn ((hη.pow_eq_one_iff_dvd n).mp h)
  have hd : (η ^ n - 1) • p.coeff n = 0 := by
    rw [sub_smul, one_smul, ← hfix, sub_self]
  have hne' : (η ^ n - 1) ≠ 0 := sub_ne_zero.mpr hne
  rcases smul_eq_zero.mp hd with h1 | h1
  · exact absurd h1 hne'
  · exact h1

end Work.EQ
