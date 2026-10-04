import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tail estimate for the weighted `ℓ²` norm `CSq`

For a coefficient family `c : (ι → ℤ) → ℂ` and a radius `R ≥ 1`, the part of the
weighted `ℓ²` norm `CSq s c = Σ_k ⟨k⟩^{2s} ‖c k‖²` concentrated on the frequencies
`⟨k⟩ > R` is controlled by the high-weight norm `CSq (s + 2r) c`:

  `Σ_{⟨k⟩ > R} ⟨k⟩^{2s} ‖c k‖² ≤ R^{-2r} Σ_k ⟨k⟩^{2(s+r)} ‖c k‖²`.

The point is that on the tail `⟨k⟩ > R` one has `⟨k⟩^{2s} ≤ R^{-2r} ⟨k⟩^{2(s+r)}`,
because `R ≤ ⟨k⟩` and `R > 0`.  This is the standard "weighted Cauchy–Schwarz /
interpolation" step (`R^{-2r}` plays the role of the lower bound on the weight of
the tail): it lets one upgrade a tail of an `H^s` bound into a factor `R^{-2r}` in
front of the `H^{s+2r}` bound.
-/

namespace Work.Diff.STE

theorem CSq_tail_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s r : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (c : (ι → ℤ) → ℂ)
    (h : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 2 * r) * ‖c k‖ ^ 2)) :
    (∑' k : {k : ι → ℤ // R < Work.Diff.STE.wt k},
        (Work.Diff.STE.wt k.1) ^ s * ‖c k.1‖ ^ 2)
      ≤ R ^ (-(2 * (r : ℤ))) * Work.Diff.STE.CSq (s + 2 * r) c := by
  classical
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  -- `R ^ (-(2 r)) = (R ^ (2 r))⁻¹`
  have hz : R ^ (-(2 * (r : ℤ))) = (R ^ (2 * r))⁻¹ := by
    have hcast : (2 * (r : ℤ)) = ((2 * r : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, zpow_neg, zpow_natCast]
  -- Pointwise bound for a frequency on the tail: `⟨k⟩^s ≤ R^{-2r} ⟨k⟩^{s+2r}`.
  have key : ∀ k : ι → ℤ, R < wt k → (wt k) ^ s ≤ R ^ (-(2 * (r : ℤ))) * (wt k) ^ (s + 2 * r) := by
    intro k hk
    have hRk : R ≤ wt k := le_of_lt hk
    have hwtk : (0 : ℝ) ≤ wt k := le_of_lt (wt_pos k)
    have hkey : R ^ (2 * r) * (wt k) ^ s ≤ (wt k) ^ (s + 2 * r) := by
      have ha : R ^ (2 * r) ≤ (wt k) ^ (2 * r) := pow_le_pow_left₀ (le_of_lt hRpos) hRk _
      have hb : R ^ (2 * r) * (wt k) ^ s ≤ (wt k) ^ (2 * r) * (wt k) ^ s :=
        mul_le_mul_of_nonneg_right ha (pow_nonneg hwtk s)
      have hc : (wt k) ^ (2 * r) * (wt k) ^ s = (wt k) ^ (s + 2 * r) := by
        rw [← pow_add, Nat.add_comm]
      linarith [hb, hc]
    rw [hz, le_inv_mul_iff₀ (pow_pos hRpos _)]
    exact hkey
  have hGsum : Summable (fun k : ι → ℤ => (R ^ (2 * r))⁻¹ * ((wt k) ^ (s + 2 * r) * ‖c k‖ ^ 2)) :=
    h.mul_left _
  -- Pointwise bound between the indicator of the tail and the high-weight summand.
  have hpt : ∀ k : ι → ℤ,
      Set.indicator {k : ι → ℤ | R < wt k} (fun k => (wt k) ^ s * ‖c k‖ ^ 2) k
        ≤ (R ^ (2 * r))⁻¹ * ((wt k) ^ (s + 2 * r) * ‖c k‖ ^ 2) := by
    intro k
    by_cases hk : k ∈ {k : ι → ℤ | R < wt k}
    · rw [Set.indicator_of_mem hk]
      have hk' : R < wt k := hk
      have h1 := key k hk'
      calc (wt k) ^ s * ‖c k‖ ^ 2
          ≤ (R ^ (-(2 * (r : ℤ))) * (wt k) ^ (s + 2 * r)) * ‖c k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = R ^ (-(2 * (r : ℤ))) * ((wt k) ^ (s + 2 * r) * ‖c k‖ ^ 2) := by ring
        _ = (R ^ (2 * r))⁻¹ * ((wt k) ^ (s + 2 * r) * ‖c k‖ ^ 2) := by rw [hz]
    · rw [Set.indicator_of_notMem hk]
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hRpos) _))
        (mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) _) (sq_nonneg _))
  have hFsum : Summable (fun k : ι → ℤ =>
      Set.indicator {k : ι → ℤ | R < wt k} (fun k => (wt k) ^ s * ‖c k‖ ^ 2) k) :=
    Summable.of_nonneg_of_le
      (fun k => Set.indicator_nonneg
        (fun a _ => mul_nonneg (pow_nonneg (le_of_lt (wt_pos a)) _) (sq_nonneg _)) k)
      hpt hGsum
  have hle := Summable.tsum_le_tsum hpt hFsum hGsum
  rw [tsum_mul_left] at hle
  have hsub := tsum_subtype ({k : ι → ℤ | R < wt k} : Set (ι → ℤ))
    (fun k : ι → ℤ => (wt k) ^ s * ‖c k‖ ^ 2)
  rw [show (∑' k : {k : ι → ℤ // R < wt k}, (wt k.1) ^ s * ‖c k.1‖ ^ 2)
      = ∑' k : ({k : ι → ℤ | R < wt k} : Set (ι → ℤ)), (wt k.1) ^ s * ‖c k.1‖ ^ 2
      from rfl,
    hsub, hz]
  simpa [CSq] using hle

end Work.Diff.STE
