/-
# `Work.R1G.gTest_hvan` — the uniform angular vanishing of the visible test perturbation

The perturbation `g = gTest ε` of `Work.R1G.GTest` is `g(z,θ) = ε·z²e^{-z}·sin(2θ)`; this
module proves the `hvan` field of `Work.ConstructionInstance.ProfileData` for it:

  `|gTest ε z θ| ≤ 4·ε·Γ(β,θ)`,  `Γ(β,θ) = (sinθ cos²θ)^β`,

for `0 ≤ β ≤ 1/3` and `0 ≤ ε`, on the closed quadrant `z ≥ 0`, `θ ∈ [0,π/2]`.

The estimate splits into the two factors:

* the radial one, `z²e^{-z} ≤ 2` for `z ≥ 0` (`gPhi_abs_le_two`), from `1 + z + z²/2 ≤ e^z`;
* the angular one, `|sin(2θ)| ≤ 2·(sinθ cos²θ)^β` for `θ ∈ [0,π/2]` (`gPsi_abs_le_two_Gamma`),
  which is the content of the exponent restriction `β ≤ 1/3`: writing `s = sinθ`, `c = cosθ`
  (both in `[0,1]` there), `sin(2θ) = 2sc` and, since `s ≤ s^β` and `c ≤ c^{2β}` for
  `0 ≤ β ≤ 1/3`,

    `sc ≤ s^β c^{2β} = (s c²)^β = Γ(β,θ)`.

The constant `4 = 2 (radial) × 2 (angular)` is what the `hvan` field consumes
(with `Cv = 4ε`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.GTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Set

namespace Work.R1G

/-! ## The radial factor -/

/-- The radial factor `gPhi z = z²e^{-z}` is bounded by `2` on `[0,∞)`.
Indeed `z²/2 ≤ 1 + z + z²/2 ≤ e^z` for `z ≥ 0`, whence `z²e^{-z} ≤ 2`. -/
lemma gPhi_abs_le_two (z : ℝ) (hz : 0 ≤ z) : |gPhi z| ≤ 2 := by
  have h := Real.sum_le_exp_of_nonneg hz 3
  have hsum : ∑ i ∈ Finset.range 3, z ^ i / (Nat.factorial i : ℝ) = 1 + z + z ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have hz2le : z ^ 2 / 2 ≤ Real.exp z := by linarith
  unfold gPhi
  rw [abs_of_nonneg (by positivity), Real.exp_neg,
    show z ^ 2 * (Real.exp z)⁻¹ = z ^ 2 / Real.exp z by rw [div_eq_mul_inv],
    div_le_iff₀ (Real.exp_pos z)]
  linarith

/-! ## The angular factor -/

/-- **The angular vanishing estimate**: on `θ ∈ [0,π/2]`, for `0 ≤ β ≤ 1/3`,

  `|sin(2θ)| ≤ 2·(sinθ·cos²θ)^β`.

This is exactly the factor "2" of the `hvan` bound; it fails for `β > 1/3` (at `θ → 0` the left
side is `~2θ` while the right side is `~θ^{3β}`). -/
lemma gPsi_abs_le_two_Gamma {β : ℝ} (_hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 3) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |gPsi θ| ≤ 2 * Work.ConstructionInstance.Gamma β θ := by
  have hθpi : θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθpi
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hβ1' : β ≤ 1 := by linarith
  -- `s ≤ s^β`
  have h1 : Real.sin θ ≤ Real.sin θ ^ β := by
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h]; exact Real.rpow_nonneg le_rfl β
    · have := Real.rpow_le_rpow_of_exponent_ge (x := Real.sin θ) h hs1 hβ1'
      rwa [Real.rpow_one] at this
  -- `c ≤ c^{2β}` (because `2β ≤ 1`)
  have h2β : 2 * β ≤ 1 := by linarith
  have h2 : Real.cos θ ≤ Real.cos θ ^ (2 * β) := by
    rcases eq_or_lt_of_le hc with h | h
    · rw [← h]; exact Real.rpow_nonneg le_rfl (2 * β)
    · have := Real.rpow_le_rpow_of_exponent_ge (x := Real.cos θ) h hc1 h2β
      rwa [Real.rpow_one] at this
  have hmul : Real.sin θ * Real.cos θ ≤ Real.sin θ ^ β * Real.cos θ ^ (2 * β) :=
    mul_le_mul h1 h2 hc (Real.rpow_nonneg hs β)
  -- `(cos θ)²` to a real power
  have hc2 : (Real.cos θ ^ 2) ^ β = Real.cos θ ^ (2 * β) := by
    rw [(Real.rpow_ofNat (Real.cos θ) 2).symm]
    exact (Real.rpow_mul (x := Real.cos θ) hc 2 β).symm
  have hkey : Real.sin θ * Real.cos θ ≤ (Real.sin θ * Real.cos θ ^ 2) ^ β := by
    calc Real.sin θ * Real.cos θ ≤ Real.sin θ ^ β * Real.cos θ ^ (2 * β) := hmul
      _ = Real.sin θ ^ β * (Real.cos θ ^ 2) ^ β := by rw [← hc2]
      _ = (Real.sin θ * Real.cos θ ^ 2) ^ β :=
          (Real.mul_rpow (x := Real.sin θ) (y := Real.cos θ ^ 2) (z := β)
            hs (sq_nonneg _)).symm
  rw [gPsi, Real.sin_two_mul, Work.ConstructionInstance.Gamma,
    abs_of_nonneg (by positivity)]
  linarith

/-! ## The estimate -/

/-- **The uniform angular vanishing of `gTest ε`**: `|gTest ε z θ| ≤ 4ε·Γ(β,θ)` for `0 ≤ ε`,
`0 ≤ β ≤ 1/3`, `z ≥ 0`, `θ ∈ [0,π/2]`.  This is the `hvan` field of
`Work.ConstructionInstance.ProfileData` for the visible test perturbation, with `Cv = 4ε`. -/
theorem gTest_hvan {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 3) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |gTest ε z θ| ≤ 4 * ε * Work.ConstructionInstance.Gamma β θ := by
  intro z θ hz hθ
  have hphi : |gPhi z| ≤ 2 := gPhi_abs_le_two z hz
  have hpsi : |gPsi θ| ≤ 2 * Work.ConstructionInstance.Gamma β θ :=
    gPsi_abs_le_two_Gamma hβ0 hβ1 hθ
  have hG0 : 0 ≤ Work.ConstructionInstance.Gamma β θ :=
    Work.ConstructionInstance.Gamma_nonneg hθ
  rw [gTest_apply, abs_mul, abs_mul, abs_of_nonneg hε]
  have h1 : |gPhi z| * |gPsi θ| ≤ 2 * (2 * Work.ConstructionInstance.Gamma β θ) :=
    mul_le_mul hphi hpsi (abs_nonneg _) (by linarith)
  calc ε * |gPhi z| * |gPsi θ| = ε * (|gPhi z| * |gPsi θ|) := by ring
    _ ≤ ε * (2 * (2 * Work.ConstructionInstance.Gamma β θ)) :=
        mul_le_mul_of_nonneg_left h1 hε
    _ = 4 * ε * Work.ConstructionInstance.Gamma β θ := by ring

end Work.R1G
