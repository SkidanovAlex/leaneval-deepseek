import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux
import Submission.Work.FatouDeg.Petal.orbitBoundsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

open Filter Set

/-- **One-step geometric decay of the defect along the orbit.**

If `a ≥ 0`, `k ≥ 1`, `a ^ (m-1) ≤ B⁻¹` and `c * k ≤ B`, then
`a ^ m ≤ ((c * k) ^ (m / (m-1)))⁻¹`.  This is the pointwise comparison used to dominate the
defect series by the `p`-series with `p = m / (m-1) > 1`. -/
private lemma pow_bound (m : ℕ) (hm : 3 ≤ m) {c : ℝ} (hc : 0 < c) {a B : ℝ} (ha : 0 ≤ a)
    {k : ℕ} (hk : 1 ≤ k) (h : a ^ (m - 1) ≤ B⁻¹) (hcB : c * (k:ℝ) ≤ B) :
    a ^ m ≤ ((c * (k:ℝ)) ^ ((m:ℝ)/(m-1)))⁻¹ := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hckpos : 0 < c * (k:ℝ) := mul_pos hc hkpos
  have hden : 0 < (m:ℝ) - 1 := by
    have : (1:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 1 < m)
    linarith
  have hp0 : 0 ≤ (m:ℝ)/(m-1) := div_nonneg (Nat.cast_nonneg m) hden.le
  have hle : B⁻¹ ≤ (c * (k:ℝ))⁻¹ := inv_anti₀ hckpos hcB
  have hstep : a ^ (m-1) ≤ (c * (k:ℝ))⁻¹ := le_trans h hle
  have hkey : (a ^ (m-1) : ℝ) ^ ((m:ℝ)/(m-1)) ≤ ((c * (k:ℝ)) ^ ((m:ℝ)/(m-1)))⁻¹ := by
    rw [← Real.inv_rpow hckpos.le]
    exact Real.rpow_le_rpow (by positivity) hstep hp0
  have hEq : (a ^ (m-1) : ℝ) ^ ((m:ℝ)/(m-1)) = a ^ m := by
    rw [← Real.rpow_natCast a (m-1), ← Real.rpow_mul ha]
    rw [show (((m-1 : ℕ) : ℝ) * ((m:ℝ)/(m-1))) = (m:ℝ) by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; field_simp; ring]
    rw [Real.rpow_natCast]
  rw [hEq] at hkey
  exact hkey

/-- The majorant `k ↦ C * ((c*k) ^ (m/(m-1)))⁻¹` is summable, since `m/(m-1) > 1`. -/
private lemma summable_majorant (m : ℕ) (hm : 3 ≤ m) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    Summable (fun k : ℕ => C * ((c * (k:ℝ)) ^ ((m:ℝ)/(m-1)))⁻¹) := by
  have hden : 0 < (m:ℝ) - 1 := by
    have : (1:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 1 < m)
    linarith
  have hp1 : 1 < (m:ℝ)/((m:ℝ)-1) := by
    rw [one_lt_div hden]; linarith
  have hg : Summable (fun n : ℕ => C * (c^((m:ℝ)/((m:ℝ)-1)))⁻¹ * ((n:ℝ)^((m:ℝ)/((m:ℝ)-1)))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr hp1).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hval : C * ((c * (n:ℝ)) ^ ((m:ℝ)/((m:ℝ)-1)))⁻¹
      = C * (c^((m:ℝ)/((m:ℝ)-1)))⁻¹ * ((n:ℝ)^((m:ℝ)/((m:ℝ)-1)))⁻¹ := by
    rw [Real.mul_rpow hc.le hnpos.le, mul_inv]
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hval]

/-- Pointwise domination of the defect along the orbit by the summable majorant, uniformly in `z`
over the whole working domain. -/
private lemma defect_bound (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {ρ c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hmap : Set.MapsTo (Pfun m G) (Dom m ρ) (Dom m ρ))
    (hnorm : ∀ z ∈ Dom m ρ, ‖Pfun m G z‖ ≤ ‖z‖)
    (hcontract : ∀ z ∈ Dom m ρ, (‖z‖ ^ (m - 1))⁻¹ + c ≤ (‖Pfun m G z‖ ^ (m - 1))⁻¹)
    (hdefect : ∀ z ∈ Dom m ρ, ‖Rfun m G z‖ ≤ C * ‖z‖ ^ m)
    {z : ℂ} (hz : z ∈ Dom m ρ) {k : ℕ} (hk : 1 ≤ k) :
    ‖Rfun m G ((Pfun m G)^[k] z)‖ ≤ C * ((c * (k:ℝ)) ^ ((m:ℝ)/(m-1)))⁻¹ := by
  obtain ⟨-, h2, -⟩ := orbitBoundsAux m hm G hc hmap hnorm hcontract
  have hmem : ∀ k : ℕ, (Pfun m G)^[k] z ∈ Dom m ρ := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact hmap ih
  have hinv : 0 ≤ (‖z‖ ^ (m - 1))⁻¹ := inv_nonneg.mpr (by positivity)
  have hkey := pow_bound m hm hc (norm_nonneg _) hk (h2 z hz k)
    (le_add_of_nonneg_left hinv)
  calc ‖Rfun m G ((Pfun m G)^[k] z)‖ ≤ C * ‖(Pfun m G)^[k] z‖ ^ m := hdefect _ (hmem k)
    _ ≤ C * ((c * (k:ℝ)) ^ ((m:ℝ)/(m-1)))⁻¹ := mul_le_mul_of_nonneg_left hkey hC

/-- **The defect series converges pointwise and locally uniformly on the working domain.**

Under the standing hypotheses (`Dom m ρ` is `P`-invariant, `P` does not increase the modulus, the
chart `(‖z‖^(m-1))⁻¹` grows by `c > 0` at each step, and `‖Rfun m G z‖ ≤ C ‖z‖^m` on `Dom m ρ`),
the series of defects along an orbit is summable and, as a series of functions of `z`, converges
locally uniformly on `Dom m ρ`.

Proof idea: `orbitBoundsAux` gives `‖P^[k] z‖^(m-1) ≤ ((‖z‖^(m-1))⁻¹ + c*k)⁻¹`, hence
`‖Rfun m G (P^[k] z)‖ ≤ C * ((‖z‖^(m-1))⁻¹ + c*k)^(-m/(m-1)) ≤ C * (c*k)^(-m/(m-1))` for `k ≥ 1`
(the last because `(‖z‖^(m-1))⁻¹ > 0`).  Since `m ≥ 4` we have `m/(m-1) > 1`, so
`k ↦ C * (c*k)^(-m/(m-1))` is summable (`Real.summable_nat_rpow_inv`), and
`SummableLocallyUniformlyOn.of_locally_bounded_eventually` applies (the bound is independent of
`z`, so it holds on every compact subset).  Pointwise summability follows from
`HasSumLocallyUniformlyOn.hasSum`. -/
theorem rfunSummableUniform (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {ρ c C : ℝ}
    (hρ : 0 < ρ) (hc : 0 < c) (hC : 0 ≤ C)
    (hmap : Set.MapsTo (Pfun m G) (Dom m ρ) (Dom m ρ))
    (hnorm : ∀ z ∈ Dom m ρ, ‖Pfun m G z‖ ≤ ‖z‖)
    (hcontract : ∀ z ∈ Dom m ρ, (‖z‖ ^ (m - 1))⁻¹ + c ≤ (‖Pfun m G z‖ ^ (m - 1))⁻¹)
    (hdefect : ∀ z ∈ Dom m ρ, ‖Rfun m G z‖ ≤ C * ‖z‖ ^ m) :
    (∀ z ∈ Dom m ρ, Summable (fun k : ℕ => Rfun m G ((Pfun m G)^[k] z))) ∧
      SummableLocallyUniformlyOn (fun k z => Rfun m G ((Pfun m G)^[k] z)) (Dom m ρ) := by
  have _ := hρ
  have hv : Summable (fun k : ℕ => C * ((c * (k:ℝ)) ^ ((m:ℝ)/(m-1)))⁻¹) :=
    summable_majorant m hm hc hC
  have hbd : ∀ z ∈ Dom m ρ, ∀ k : ℕ, 1 ≤ k →
      ‖Rfun m G ((Pfun m G)^[k] z)‖ ≤ C * ((c * (k:ℝ)) ^ ((m:ℝ)/(m-1)))⁻¹ :=
    fun z hz k hk => defect_bound m hm G hc hC hmap hnorm hcontract hdefect hz hk
  refine ⟨?_, ?_⟩
  · intro z hz
    refine Summable.of_norm_bounded_eventually_nat hv ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    exact hbd z hz k hk
  · apply SummableLocallyUniformlyOn.of_locally_bounded_eventually (isOpen_Dom m ρ)
    intro K hK _
    refine ⟨fun k => C * ((c * (k:ℝ)) ^ ((m:ℝ)/(m-1)))⁻¹, hv, ?_⟩
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton (0:ℕ)) ?_
    intro n hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    push Not at hn
    obtain ⟨x, hxK, hxbd⟩ := hn
    exact absurd (hbd x (hK hxK) n (by omega)) (not_le.mpr hxbd)

end Work.FatouDeg.Petal
