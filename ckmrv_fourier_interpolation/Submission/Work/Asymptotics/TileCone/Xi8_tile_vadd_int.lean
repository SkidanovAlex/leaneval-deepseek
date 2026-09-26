/-
# The numerator `Ξ₈` on the cusp-`±1` tiles

`Work.Asymptotics.Xi8` is the numerator of the CKMRV kernel `K⁺` in dimension `8`
(`Submission/Work/Asymptotics/KPlusXiDefs.lean`); it is a polynomial in the `SL(2,ℤ)`-atoms
`E₂, E₄, E₆, Δ` of the two variables `τ` and `z`.  This file bounds it on the two cusp-`±1`
tiles `τ = n +ᵥ w` (`n = ±1`, `w ∈ E = KEpsilon = S(𝓕)`), in the shape

  `‖Ξ₈(n + w, z)‖ ≤ C (scale w)^N (1 + exp (2π (Im (S•w) − Im z)))`   (`1 ≤ Im z`),

which is the `hXi` input of the tile-cone route: the exponential factor
`exp (2π (Im (S•w) − Im z))` is exactly the one carried by the cone divisor lower bound, so the
two cancel in `‖Ξ₈‖ / ‖Δ(z)(j τ − j z)‖`.

## Proof

`Xi8_cancelled` writes `Ξ₈` as a difference of three products, each of one `τ`-factor and one
`z`-factor:

  `Ξ₈(τ,z) = Δ(z)/Δ(τ)·E₄(τ)²Φ₈(τ)
              − τ·E₆(τ)·E₄(z)²(E₄(z) − E₂(z)²)
              − 2φ₀(τ)E₄(τ)·E₄(z)(E₂(z)E₆(z) − E₄(z)²)`.

On the `z`-side (`Im z ≥ 1`) the three factors are `O(q(z))`, `O(q(z))` and `O(1)` by the cusp
estimates of `KPlusXiDefs` (`DeltaFun_isBigOq_one`, `delta1_isBigOq`, `eps_isBigOq`,
`E4Fun_bound`).  On the `τ`-side all three `τ`-factors are moderate *up to the single exponential
`e^{2π Im (S•w)}`*: this is the weight calculus `EtailE.Bdd` of
`Submission/Work/Asymptotics/EtailE/Shapes.lean`, whose atoms on the tiles are the inventory of
`Submission/Work/Asymptotics/tile_Bdd_atoms.lean`.  The only new atom is `Φ₈`, assembled from
`E₂, E₄, E₆, φ₀, φ₂` by the closure of `Bdd` under products, sums and scalar multiples.  The two
sides are then combined by the triangle inequality and the elementary
`‖q(z)‖ = e^{−2π Im z} ≤ 1`.
-/
import Mathlib
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KPlusFunnel.Atoms
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.EtailE.Atoms

namespace Work.Asymptotics.TileCone

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Auxiliary shape lemmas -/

/-- Monotonicity of `C 𝓢^N E` in `C` and in `N`, for `𝓢 ≥ 1`. -/
private lemma shape_mono {𝓢 C N C' N' E : ℝ} (h𝓢 : 1 ≤ 𝓢) (hC : C ≤ C') (hN : N ≤ N')
    (hE : 0 ≤ E) (hC'0 : 0 ≤ C') : C * 𝓢 ^ N * E ≤ C' * 𝓢 ^ N' * E := by
  refine mul_le_mul_of_nonneg_right ?_ hE
  exact mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le h𝓢 hN)
    (Real.rpow_nonneg (le_trans zero_le_one h𝓢) N) hC'0

/-- Three `Bdd` estimates, at a common constant and a common exponent. -/
private lemma bdd_three {c : ℝ} {F G K : ℍ → ℂ} (hF : EtailE.Bdd c F) (hG : EtailE.Bdd c G)
    (hK : EtailE.Bdd c K) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : ℍ, w ∈ KEpsilon →
      ‖F w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) ∧
      ‖G w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) ∧
      ‖K w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := hG
  obtain ⟨C3, N3, hC3, hN3, h3⟩ := hK
  refine ⟨C1 + C2 + C3, max N1 (max N2 N3), by positivity, le_max_of_le_left hN1, fun w hw => ?_⟩
  have hs : (1 : ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hC' : (0 : ℝ) ≤ C1 + C2 + C3 := by positivity
  have hE' : (0 : ℝ) ≤ Real.exp (c * (ModularGroup.S • w).im) := Real.exp_nonneg _
  have hN1' : N1 ≤ max N1 (max N2 N3) := le_max_left _ _
  have hN2' : N2 ≤ max N1 (max N2 N3) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN3' : N3 ≤ max N1 (max N2 N3) := le_trans (le_max_right _ _) (le_max_right _ _)
  exact ⟨le_trans (h1 w hw) (shape_mono hs (by linarith) hN1' hE' hC'),
    le_trans (h2 w hw) (shape_mono hs (by linarith) hN2' hE' hC'),
    le_trans (h3 w hw) (shape_mono hs (by linarith) hN3' hE' hC')⟩

/-- The `τ`-atom `Φ₈ = E₄(τE₆ − 2φ₀E₄) + E₆φ₂` is moderate on the cusp-`±1` tiles. -/
private lemma phi8_bdd (n : ℤ) (hn : n = 1 ∨ n = -1) :
    EtailE.Bdd 0 (fun w : ℍ => phi8 ((n : ℝ) +ᵥ w)) := by
  have hτ : EtailE.Bdd 0 (fun w : ℍ => (((n : ℝ) +ᵥ w : ℍ) : ℂ)) := Bdd.vadd n hn
  have h4 : EtailE.Bdd 0 (fun w : ℍ => E4Fun ((n : ℝ) +ᵥ w)) := Bdd.vadd_E4 n hn
  have h6 : EtailE.Bdd 0 (fun w : ℍ => E6Fun ((n : ℝ) +ᵥ w)) := Bdd.vadd_E6 n hn
  have h0 : EtailE.Bdd 0 (fun w : ℍ => phi0 ((n : ℝ) +ᵥ w)) := by
    refine EtailE.Bdd.congr ?_ (Bdd.vadd_phi1 n hn)
    funext w
    rfl
  have h2 : EtailE.Bdd 0 (fun w : ℍ => phi2 ((n : ℝ) +ᵥ w)) := by
    refine EtailE.Bdd.congr ?_ (Bdd.vadd_phi2 n hn)
    funext w
    rfl
  have h2' : EtailE.Bdd 0 (fun w : ℍ => 2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)) := by
    refine EtailE.Bdd.congr ?_ (EtailE.Bdd.const_mul (2 : ℂ) (EtailE.Bdd.mul_zero h0 h4))
    funext w
    ring
  have h3 : EtailE.Bdd 0 (fun w : ℍ => (((n : ℝ) +ᵥ w : ℍ) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      - 2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)) :=
    (EtailE.Bdd.mul_zero hτ h6).sub h2'
  have hmain := (EtailE.Bdd.mul_zero h4 h3).add (EtailE.Bdd.mul_zero h6 h2)
  refine EtailE.Bdd.congr ?_ hmain
  funext w
  simp only [phi8]

/-! ## The bound on one tile -/

/-- The bound of the theorem, for a fixed `n = ±1` (the constants are allowed to depend on `n`). -/
private theorem xi8_tile_fixed (n : ℤ) (hn : n = 1 ∨ n = -1) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ), w ∈ KEpsilon → ∀ z : ℍ, 1 ≤ z.im →
      ‖Xi8 ((n : ℝ) +ᵥ w) z‖
        ≤ C * (scale w) ^ N
            * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im))) := by
  -- `z`-side atoms at the cusp `i∞`
  obtain ⟨Cq, hCq, hΔzb⟩ := DeltaFun_isBigOq_one
  obtain ⟨Cs, hCs, hσb⟩ := delta1_isBigOq
  obtain ⟨Ce, hCe, hεb⟩ := eps_isBigOq
  obtain ⟨CE4, hCE4, hE4b⟩ := E4Fun_bound
  -- `w`-side atoms on the tile `n + E`
  have hID : EtailE.Bdd (2 * Real.pi) (fun w : ℍ => (DeltaFun ((n : ℝ) +ᵥ w))⁻¹) :=
    Bdd.shift EtailE.E_bdd_invDelta (fun τ => by rw [KernelFacts.DeltaFun_vadd_one]) n hn
  have hτ : EtailE.Bdd 0 (fun w : ℍ => (((n : ℝ) +ᵥ w : ℍ) : ℂ)) := Bdd.vadd n hn
  have h4 : EtailE.Bdd 0 (fun w : ℍ => E4Fun ((n : ℝ) +ᵥ w)) := Bdd.vadd_E4 n hn
  have h6 : EtailE.Bdd 0 (fun w : ℍ => E6Fun ((n : ℝ) +ᵥ w)) := Bdd.vadd_E6 n hn
  have h0 : EtailE.Bdd 0 (fun w : ℍ => phi0 ((n : ℝ) +ᵥ w)) := by
    refine EtailE.Bdd.congr ?_ (Bdd.vadd_phi1 n hn)
    funext w
    rfl
  have hΦ : EtailE.Bdd 0 (fun w : ℍ => phi8 ((n : ℝ) +ᵥ w)) := phi8_bdd n hn
  -- the three `τ`-factors, at the common shape `C (scale w)^N e^{2π Im (S•w)}`
  have hF1 : EtailE.Bdd (2 * Real.pi) (fun w : ℍ => (DeltaFun ((n : ℝ) +ᵥ w))⁻¹
      * E4Fun ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)) := by
    have h := ((hID.mul h4).mul h4).mul hΦ
    simpa only [add_zero] using h
  have hF2 : EtailE.Bdd (2 * Real.pi)
      (fun w : ℍ => (((n : ℝ) +ᵥ w : ℍ) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.mono (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (EtailE.Bdd.mul_zero hτ h6)
  have hF3 : EtailE.Bdd (2 * Real.pi)
      (fun w : ℍ => 2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)) := by
    have h : EtailE.Bdd 0 (fun w : ℍ => 2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)) := by
      refine EtailE.Bdd.congr ?_ (EtailE.Bdd.const_mul (2 : ℂ) (EtailE.Bdd.mul_zero h0 h4))
      funext w
      ring
    exact EtailE.Bdd.mono (by positivity : (0 : ℝ) ≤ 2 * Real.pi) h
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := bdd_three hF1 hF2 hF3
  refine ⟨C1 * (Cq + CE4 ^ 2 * Cs + CE4 * Ce), N1, by positivity, hN1, ?_⟩
  intro w hw z hz
  let τ : ℍ := (n : ℝ) +ᵥ w
  have hτeq : τ = (n : ℝ) +ᵥ w := rfl
  obtain ⟨hw1, hw2, hw3⟩ := hb1 w hw
  -- `z`-side bounds
  have hΔz : ‖DeltaFun z‖ ≤ Cq * ‖qParamFun z‖ := by
    have h := hΔzb z hz
    simpa using h
  have hσz : ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cs * ‖qParamFun z‖ := by
    have h := hσb z hz
    simpa using h
  have hεz : ‖E2Fun z * E6Fun z - E4Fun z ^ 2‖ ≤ Ce * ‖qParamFun z‖ := by
    have h := hεb z hz
    have h' : ‖E4Fun z ^ 2 - E6Fun z * E2Fun z‖ ≤ Ce * ‖qParamFun z‖ := by simpa using h
    rwa [show E2Fun z * E6Fun z - E4Fun z ^ 2
        = -(E4Fun z ^ 2 - E6Fun z * E2Fun z) by ring, norm_neg]
  have hE4z : ‖E4Fun z‖ ≤ CE4 := hE4b z hz
  have hZ2 : ‖E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖ ≤ (CE4 ^ 2 * Cs) * ‖qParamFun z‖ := by
    rw [norm_mul, norm_pow]
    calc ‖E4Fun z‖ ^ 2 * ‖E4Fun z - E2Fun z ^ 2‖
        ≤ CE4 ^ 2 * (Cs * ‖qParamFun z‖) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4z 2) hσz (norm_nonneg _)
            (by positivity)
      _ = (CE4 ^ 2 * Cs) * ‖qParamFun z‖ := by ring
  have hZ3 : ‖E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
      ≤ (CE4 * Ce) * ‖qParamFun z‖ := by
    rw [norm_mul]
    calc ‖E4Fun z‖ * ‖E2Fun z * E6Fun z - E4Fun z ^ 2‖
        ≤ CE4 * (Ce * ‖qParamFun z‖) :=
          mul_le_mul hE4z hεz (norm_nonneg _) (by positivity)
      _ = (CE4 * Ce) * ‖qParamFun z‖ := by ring
  have hW0 : (0 : ℝ) ≤ C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
    mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N1))
      (Real.exp_nonneg _)
  -- the three terms of `Xi8_cancelled`
  have hT1 : ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
      ≤ (Cq * ‖qParamFun z‖)
          * (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by
    rw [show DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
        = DeltaFun z * ((DeltaFun τ)⁻¹ * E4Fun τ * E4Fun τ * phi8 τ) by
      rw [div_eq_mul_inv]; ring]
    rw [norm_mul]
    exact mul_le_mul hΔz hw1 (norm_nonneg _) (mul_nonneg hCq.le (norm_nonneg _))
  have hT2 : ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
      ≤ (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
          * ((CE4 ^ 2 * Cs) * ‖qParamFun z‖) := by
    rw [show (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)
        = ((τ : ℂ) * E6Fun τ) * (E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)) by ring]
    rw [norm_mul]
    exact mul_le_mul hw2 hZ2 (norm_nonneg _) hW0
  have hT3 : ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
      ≤ (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
          * ((CE4 * Ce) * ‖qParamFun z‖) := by
    rw [show 2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)
        = (2 * phi0 τ * E4Fun τ) * (E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)) by ring]
    rw [norm_mul]
    exact mul_le_mul hw3 hZ3 (norm_nonneg _) hW0
  -- triangle inequality and the sum
  have htri : ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
        - (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)
        - 2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
      ≤ ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
        + ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
        + ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖ := by
    have h1 := norm_sub_le (DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
        - (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2))
      (2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2))
    have h2 := norm_sub_le (DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ)
      ((τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2))
    linarith
  have hsum : ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
        + ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
        + ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
      ≤ (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
          * (Cq + CE4 ^ 2 * Cs + CE4 * Ce) * ‖qParamFun z‖ := by
    calc ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
          + ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
          + ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
        ≤ (Cq * ‖qParamFun z‖)
            * (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
          + (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
            * ((CE4 ^ 2 * Cs) * ‖qParamFun z‖)
          + (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
            * ((CE4 * Ce) * ‖qParamFun z‖) := by linarith [hT1, hT2, hT3]
      _ = (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
            * (Cq + CE4 ^ 2 * Cs + CE4 * Ce) * ‖qParamFun z‖ := by ring
  have hXi : ‖Xi8 ((n : ℝ) +ᵥ w) z‖
      ≤ (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
          * (Cq + CE4 ^ 2 * Cs + CE4 * Ce) * ‖qParamFun z‖ := by
    rw [Xi8_cancelled ((n : ℝ) +ᵥ w) z (ClassicalFacts.DeltaFun_ne_zero _)
      (ClassicalFacts.DeltaFun_ne_zero _)]
    exact le_trans htri hsum
  -- the two exponentials
  have hexp : Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * ‖qParamFun z‖
      = Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) := by
    rw [MFix.norm_qParamFun z, ← Real.exp_add]
    congr 1
    ring
  have hKpos : (0 : ℝ) < C1 * (Cq + CE4 ^ 2 * Cs + CE4 * Ce) := by positivity
  have he0 : (0 : ℝ) ≤ Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) :=
    Real.exp_nonneg _
  have hsc0 : (0 : ℝ) ≤ (scale w) ^ N1 := Real.rpow_nonneg (Work.Kernels.scale_pos w).le N1
  calc ‖Xi8 ((n : ℝ) +ᵥ w) z‖
      ≤ (C1 * (scale w) ^ N1 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
          * (Cq + CE4 ^ 2 * Cs + CE4 * Ce) * ‖qParamFun z‖ := hXi
    _ = (C1 * (Cq + CE4 ^ 2 * Cs + CE4 * Ce)) * (scale w) ^ N1
          * (Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * ‖qParamFun z‖) := by ring
    _ = (C1 * (Cq + CE4 ^ 2 * Cs + CE4 * Ce)) * (scale w) ^ N1
          * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) := by rw [hexp]
    _ ≤ (C1 * (Cq + CE4 ^ 2 * Cs + CE4 * Ce)) * (scale w) ^ N1
          * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im))) :=
        mul_le_mul_of_nonneg_left (by linarith [he0])
          (mul_nonneg hKpos.le hsc0)

/-! ## The two tiles -/

theorem Xi8_tile_vadd_int :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖Work.Asymptotics.Xi8 ((n : ℝ) +ᵥ w) z‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im))) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := xi8_tile_fixed 1 (Or.inl rfl)
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := xi8_tile_fixed (-1) (Or.inr rfl)
  refine ⟨C1 + C2, max N1 N2, by positivity, le_max_of_le_left hN1, ?_⟩
  intro w hw n hn z hz
  have hs : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs
  have he0 : (0 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) := by
    positivity
  have hC12 : (0 : ℝ) ≤ C1 + C2 := by linarith
  have step1 : C1 * (Work.Kernels.scale w) ^ N1
      ≤ (C1 + C2) * (Work.Kernels.scale w) ^ (max N1 N2) :=
    mul_le_mul (show C1 ≤ C1 + C2 by linarith)
      (Real.rpow_le_rpow_of_exponent_le hs (le_max_left N1 N2))
      (Real.rpow_nonneg hs0 N1) hC12
  have step2 : C2 * (Work.Kernels.scale w) ^ N2
      ≤ (C1 + C2) * (Work.Kernels.scale w) ^ (max N1 N2) :=
    mul_le_mul (show C2 ≤ C1 + C2 by linarith)
      (Real.rpow_le_rpow_of_exponent_le hs (le_max_right N1 N2))
      (Real.rpow_nonneg hs0 N2) hC12
  rcases hn with h | h
  · subst h
    exact le_trans (hb1 w hw z hz) (mul_le_mul_of_nonneg_right step1 he0)
  · subst h
    exact le_trans (hb2 w hw z hz) (mul_le_mul_of_nonneg_right step2 he0)

end

end Work.Asymptotics.TileCone
