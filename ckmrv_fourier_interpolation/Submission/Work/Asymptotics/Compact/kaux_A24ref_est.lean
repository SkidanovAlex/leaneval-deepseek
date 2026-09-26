/-
# The reference atom `A24ref` is `O(1 + ‖z‖)` for `τ` in a compact set

`A24ref ℓ τ z = -3456 Δ(τ) E14ref(z) Lref(ℓ,z) - (ψ₂(τ)E₁₀(τ) - ψ₄(τ)E₈(τ)) E10ref(z) D2ref(z)`
is the value of the bracket atom `A24` with every `z`-atom replaced by its cusp reference
expansion (`E14ref`, `E10ref`, `D2ref`, `Lref`, defined in `kminus_tail_core`).

Once the reference atoms are *explicit polynomials in `e = Ept z`* of degree `≤ 2`, the
estimate is elementary: for `z.im ≥ 1` one has `‖e‖ ≤ 1`, so `‖E14ref z‖ ≤ 25`,
`‖E10ref z‖ ≤ 265`, `‖D2ref z‖ ≤ 161`, while `‖Lref ℓ z‖ ≤ (π + ‖cuspC ℓ‖ + 20)(1 + ‖z‖)`
by `norm_Xc_le`.  The `τ`-atoms `Δ(τ)` and `ψ₂(τ)E₁₀(τ) - ψ₄(τ)E₈(τ)` are continuous, hence
bounded on the compact `K`.
-/
import Mathlib
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_bounds
import Submission.Work.Asymptotics.Compact.kaux_A24_est
import Submission.Work.Asymptotics.Ncusp_bound_ball

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.Compact

open Work.Kernels
open Work.Residues (Ept)

/-! ## Bounds for the reference atoms at the cusp -/

/-- `‖E₁₄ref z‖ = ‖1 - 24 e²‖ ≤ 25` for `z.im ≥ 1`. -/
lemma norm_E14ref_le {z : ℍ} (hz : 1 ≤ z.im) : ‖E14ref z‖ ≤ 25 := by
  have he : ‖Ept z‖ ≤ 1 := norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) he
  have h24 : ‖(24 : ℂ) * (Ept z) ^ 2‖ = 24 * ‖(Ept z) ^ 2‖ := by
    rw [norm_mul]; norm_num
  rw [E14ref]
  calc ‖(1 : ℂ) - 24 * (Ept z) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * (Ept z) ^ 2‖ :=
        norm_sub_le _ _
    _ = 1 + 24 * ‖(Ept z) ^ 2‖ := by rw [h24, norm_one]
    _ ≤ 25 := by linarith

/-- `‖E₁₀ref z‖ = ‖1 - 264 e²‖ ≤ 265` for `z.im ≥ 1`. -/
lemma norm_E10ref_le {z : ℍ} (hz : 1 ≤ z.im) : ‖E10ref z‖ ≤ 265 := by
  have he : ‖Ept z‖ ≤ 1 := norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) he
  have h264 : ‖(264 : ℂ) * (Ept z) ^ 2‖ = 264 * ‖(Ept z) ^ 2‖ := by
    rw [norm_mul]; norm_num
  rw [E10ref]
  calc ‖(1 : ℂ) - 264 * (Ept z) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖(264 : ℂ) * (Ept z) ^ 2‖ :=
        norm_sub_le _ _
    _ = 1 + 264 * ‖(Ept z) ^ 2‖ := by rw [h264, norm_one]
    _ ≤ 265 := by linarith

/-- `‖D2ref z‖ = ‖1 + 16e - 144e²‖ ≤ 161` for `z.im ≥ 1`. -/
lemma norm_D2ref_le {z : ℍ} (hz : 1 ≤ z.im) : ‖D2ref z‖ ≤ 161 := by
  have he : ‖Ept z‖ ≤ 1 := norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) he
  have h16 : ‖(16 : ℂ) * Ept z‖ = 16 * ‖Ept z‖ := by rw [norm_mul]; norm_num
  have h144 : ‖(144 : ℂ) * (Ept z) ^ 2‖ = 144 * ‖(Ept z) ^ 2‖ := by
    rw [norm_mul]; norm_num
  rw [D2ref]
  calc ‖(1 : ℂ) + 16 * Ept z - 144 * (Ept z) ^ 2‖
      ≤ ‖(1 : ℂ) + 16 * Ept z‖ + ‖(144 : ℂ) * (Ept z) ^ 2‖ := norm_sub_le _ _
    _ ≤ (‖(1 : ℂ)‖ + ‖(16 : ℂ) * Ept z‖) + 144 * ‖(Ept z) ^ 2‖ := by
        rw [h144]
        exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 161 := by rw [h16, norm_one]; linarith

/-- `‖Lref ℓ z‖ ≤ (π + ‖cuspC ℓ‖ + 20)(1 + ‖z‖)` for `z.im ≥ 1`. -/
lemma norm_Lref_le (ℓ : LogLambdaData) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖Lref ℓ z‖ ≤ (Real.pi + ‖cuspC ℓ‖ + 20) * (1 + ‖(z : ℂ)‖) := by
  have hX := norm_Xc_le ℓ z
  have he : ‖Ept z‖ ≤ 1 := norm_Ept_le_one hz
  have h8 : ‖(8 : ℂ) * Ept z‖ = 8 * ‖Ept z‖ := by rw [norm_mul]; norm_num
  have h12 : ‖(12 : ℂ) * (Ept z) ^ 2‖ = 12 * ‖(Ept z) ^ 2‖ := by rw [norm_mul]; norm_num
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) he
  have h1 : ‖Xc ℓ z - 8 * Ept z‖ ≤ ‖Xc ℓ z‖ + 8 := by
    have h := norm_sub_le (Xc ℓ z) ((8 : ℂ) * Ept z)
    rw [h8] at h
    linarith
  have h2 : ‖(12 : ℂ) * (Ept z) ^ 2‖ ≤ 12 := by
    rw [h12]; linarith
  rw [Lref]
  calc ‖Xc ℓ z - 8 * Ept z + 12 * (Ept z) ^ 2‖
      ≤ ‖Xc ℓ z - 8 * Ept z‖ + ‖(12 : ℂ) * (Ept z) ^ 2‖ := norm_add_le _ _
    _ ≤ (‖Xc ℓ z‖ + 8) + 12 := add_le_add h1 h2
    _ ≤ (Real.pi + ‖cuspC ℓ‖ + 20) * (1 + ‖(z : ℂ)‖) := by
        have hz0 : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
        have hc0 : (0 : ℝ) ≤ ‖cuspC ℓ‖ := norm_nonneg _
        nlinarith [hX, Real.pi_pos, hz0, hc0]

/-
Goal: the same bound as `kaux_A24_est` for the reference atom
`A24ref ℓ τ z = -3456 Δ(τ) E14ref(z) Lref(ℓ,z) - (ψ₂(τ)E₁₀(τ) - ψ₄(τ)E₈(τ)) E10ref(z) D2ref(z)`,
where `E14ref z = 1 - 24(Ept z)²`, `E10ref z = 1 - 264(Ept z)²`, `D2ref z = 1 + 16 Ept z - 144 (Ept z)²`
and `Lref ℓ z = Xc ℓ z - 8 Ept z + 12 (Ept z)²` (all defined in
`Work.Asymptotics.Compact.kminus_tail_core`).  Suggested ingredients: the
`τ`-bounds from `IsCompact.exists_bound_of_continuousOn` (`continuous_psi2_ub`,
`continuous_psi4_ub`, `continuous_DeltaFun_ub`, `continuous_E6Fun_ub`), and
`Work.Asymptotics.Compact.norm_Xc_le` for `Lref`.
-/
theorem kaux_A24ref_est (ℓ : Work.Kernels.LogLambdaData) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (τ z : UpperHalfPlane), τ ∈ K → H ≤ z.im →
      ‖Work.Asymptotics.Compact.A24ref ℓ τ z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  have hE10cont : Continuous (fun τ : ℍ => E10Fun τ) :=
    continuous_E4Fun_ub.mul continuous_E6Fun_ub
  have hE8cont : Continuous (fun τ : ℍ => E8Fun τ) := continuous_E4Fun_ub.pow 2
  have hψcont : Continuous (fun τ : ℍ => psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) :=
    ((continuous_psi2_ub ℓ).mul hE10cont).sub ((continuous_psi4_ub ℓ).mul hE8cont)
  obtain ⟨Bd, hBd⟩ := hK.exists_bound_of_continuousOn continuous_DeltaFun_ub.continuousOn
  obtain ⟨Bψ, hBψ⟩ := hK.exists_bound_of_continuousOn hψcont.continuousOn
  set MΔ : ℝ := max Bd 1 with hMΔdef
  set Mψ : ℝ := max Bψ 1 with hMψdef
  have hMΔ0 : 0 < MΔ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMψ0 : 0 < Mψ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1, 3456 * MΔ * 25 * (Real.pi + ‖cuspC ℓ‖ + 20) + Mψ * 265 * 161, one_pos, ?_, ?_⟩
  · have h1 : 0 < 3456 * MΔ * 25 * (Real.pi + ‖cuspC ℓ‖ + 20) := by positivity
    have h2 : 0 < Mψ * 265 * 161 := by positivity
    linarith
  · intro τ z hτ hz
    have bE14 : ‖E14ref z‖ ≤ 25 := norm_E14ref_le hz
    have bE10 : ‖E10ref z‖ ≤ 265 := norm_E10ref_le hz
    have bD2 : ‖D2ref z‖ ≤ 161 := norm_D2ref_le hz
    have bL : ‖Lref ℓ z‖ ≤ (Real.pi + ‖cuspC ℓ‖ + 20) * (1 + ‖(z : ℂ)‖) := norm_Lref_le ℓ hz
    have bΔ : ‖DeltaFun τ‖ ≤ MΔ := le_trans (hBd τ hτ) (le_max_left _ _)
    have bψ : ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖ ≤ Mψ :=
      le_trans (hBψ τ hτ) (le_max_left _ _)
    have hone : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith [norm_nonneg (z : ℂ)]
    have h3456 : ‖(-3456 : ℂ)‖ ≤ 3456 := by norm_num
    have h25 : (0 : ℝ) ≤ 25 := by norm_num
    have ht1 : ‖-3456 * DeltaFun τ * E14ref z * Lref ℓ z‖
        ≤ 3456 * MΔ * 25 * ((Real.pi + ‖cuspC ℓ‖ + 20) * (1 + ‖(z : ℂ)‖)) :=
      norm_mul_four_le (A := 3456) (B := MΔ) (C := 25)
        (D := (Real.pi + ‖cuspC ℓ‖ + 20) * (1 + ‖(z : ℂ)‖))
        h3456 bΔ bE14 bL (by norm_num) hMΔ0.le h25
    have t1 : ‖-3456 * DeltaFun τ * E14ref z * Lref ℓ z‖
        ≤ 3456 * MΔ * 25 * (Real.pi + ‖cuspC ℓ‖ + 20) * (1 + ‖(z : ℂ)‖) :=
      le_trans ht1 (le_of_eq (by ring))
    have hnn : (0 : ℝ) ≤ Mψ * 265 * 161 := by positivity
    have t2 : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10ref z * D2ref z‖
        ≤ Mψ * 265 * 161 * (1 + ‖(z : ℂ)‖) := by
      have hbase : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10ref z * D2ref z‖
          ≤ Mψ * 265 * 161 :=
        norm_mul_three_le (A := Mψ) (B := 265) (C := 161)
          bψ bE10 bD2 hMψ0.le (by norm_num)
      calc ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10ref z * D2ref z‖
          ≤ Mψ * 265 * 161 := hbase
        _ = Mψ * 265 * 161 * 1 := by ring
        _ ≤ Mψ * 265 * 161 * (1 + ‖(z : ℂ)‖) := mul_le_mul_of_nonneg_left hone hnn
    rw [A24ref]
    refine le_trans (norm_sub_le _ _) ?_
    refine le_trans (add_le_add t1 t2) ?_
    have heq : 3456 * MΔ * 25 * (Real.pi + ‖cuspC ℓ‖ + 20) * (1 + ‖(z : ℂ)‖)
        + Mψ * 265 * 161 * (1 + ‖(z : ℂ)‖)
        = (3456 * MΔ * 25 * (Real.pi + ‖cuspC ℓ‖ + 20) + Mψ * 265 * 161)
          * (1 + ‖(z : ℂ)‖) := by ring
    rw [heq]

end Work.Asymptotics.Compact
