import Mathlib
import Submission.Work.EQ.tailP_bdd_near_puncture

namespace Work.EQ

/-- **The backward radicands of a path of chains lie in the slit plane from a uniform index.**

`γ` is a path of `EqRelC`-chains on `Ici S` whose stable parameter is bounded by `B` there.  Then
there is a uniform index `n₀` such that for every `s ≥ S` and every `m ≥ n₀` the backward radicand
of the point `(γ s).1 (m+1)` — i.e. `(x + a/2)^2 + y^2` for `(x,y) = (γ s).1 (m+1)` — lies in the
slit plane.

Proof: each point of a chain is a fan value with parameter `λ^n ψ₁` (`Work.EQ.chain_eq_fan'`
applied to `Work.EQ.shiftZ`, which needs only `IsChain`); for `λ^{m+1} B` below the fan threshold
`δf` of `Work.EQ.fan_slitPlane` this puts the radicand in the slit plane.  No `H0`-membership is
needed. -/
theorem path_slit_of_isChain {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {γ : ℝ → ChainData} {S : ℝ}
    (hγ : ∀ s, S ≤ s → IsChain a h (γ s)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, S ≤ s → ‖(γ s).2.1‖ ≤ B) :
    ∃ n₀ : ℕ, ∀ s, S ≤ s → ∀ m : ℕ, n₀ ≤ m →
      (((γ s).1 ((m : ℤ) + 1)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
        + ((γ s).1 ((m : ℤ) + 1)).2 ^ 2 ∈ Complex.slitPlane := by
  -- the fan threshold of the stable germ: below it every fan radicand is in the slit plane
  obtain ⟨δf, hδf, hslitFan⟩ := fan_slitPlane (h := h) ha0 ha1 hh
  have hl0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  -- an index from which `λ^m B < δf` for all `m`
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, (eqLam a) ^ n * B < δf := by
    rcases eq_or_lt_of_le hB0 with hz | hBpos
    · exact ⟨0, by rw [← hz, mul_zero]; exact hδf⟩
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδf hBpos) hl1
      refine ⟨n, ?_⟩
      have h2 : (eqLam a) ^ n * B < (δf / B) * B := mul_lt_mul_of_pos_right hn hBpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hBpos)] at h2
  refine ⟨n₀, fun s hs m hm => ?_⟩
  -- `(γ s).1 (m+1)` is the `0`-th point of the shift `σ^{m+1}`, hence a fan value
  have hp : IsChain a h (shiftZ a ((m : ℤ) + 1) (γ s)) :=
    isChain_shiftZ ha0 ha1 (hγ s hs) _
  obtain ⟨ε, hε⟩ := chain_eq_fan' ha0 ha1 hp
  have hpt : (γ s).1 ((m : ℤ) + 1)
      = fan a h ε (((eqLam a : ℝ) : ℂ) ^ ((m : ℤ) + 1) * (γ s).2.1) := by
    have h0 : (shiftZ a ((m : ℤ) + 1) (γ s)).1 0 = (γ s).1 ((m : ℤ) + 1) := by
      rw [shiftZ_fst, zero_add]
    rw [← h0, hε, shiftZ_psi1]
  rw [hpt]
  refine hslitFan ε _ ?_
  -- the fan parameter is small: `‖λ^{m+1} ψ₁‖ ≤ λ^{m+1} B ≤ λ^{n₀} B < δf`
  have hz : ((eqLam a : ℝ) : ℂ) ^ ((m : ℤ) + 1) * (γ s).2.1
      = ((eqLam a : ℝ) : ℂ) ^ (m + 1) * (γ s).2.1 := by
    rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hz, norm_mul, norm_pow, Complex.norm_of_nonneg hl0.le]
  have h1 : (eqLam a) ^ (m + 1) * ‖(γ s).2.1‖ ≤ (eqLam a) ^ (m + 1) * B :=
    mul_le_mul_of_nonneg_left (hB s hs) (pow_nonneg hl0.le _)
  have h2 : (eqLam a) ^ (m + 1) * B ≤ (eqLam a) ^ n₀ * B :=
    mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hl0.le hl1.le (by omega)) hB0
  linarith [h1, h2, hn₀]

end Work.EQ
