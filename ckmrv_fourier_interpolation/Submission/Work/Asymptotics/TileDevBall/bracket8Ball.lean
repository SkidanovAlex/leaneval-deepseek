/-
# The `K_-` bracket bound on the cusp-`±1` tile ball

The target `Work.Asymptotics.TileDevBall.bracket8Ball` bounds

  `‖brMinus ℓ 8 τ ζ + Sh τ ζ · br0 8 ℓ τ ζ‖ ≤ C (scale w)^N`

on the tile ball `‖ζ - S • w‖ ≤ 29/20`, `3 ≤ Im ζ`, `w ∈ E = KEpsilon`, `τ = n +ᵥ w`, `n = ±1`.

By `Work.Asymptotics.Compact.tail_identity` the quantity being bounded is exactly
`-3456π · Sh τ ζ · (K_-^{(8)}(τ,ζ) - 𝒢_-^{(8)}(τ,ζ))`, so this is the `K_-` analogue of
`Work.Asymptotics.TileDevBall.kplusDev8Ball`.

The proof uses the algebraic identity `br_add_br0_decomp` of
`Submission/Work/Asymptotics/EtailE/EtailE_KMinus8.lean`,

  `brMinus ℓ 8 τ ζ + br0 8 ℓ τ ζ
     = -3456 E₄(τ)(E₁₀(ζ)𝓛(ζ) - Xc(ζ))
       - Λ(τ)·(E₈(ζ)W(ζ) - E₆(ζ)(U(ζ)² - V(ζ)²))
       + 1728 ψ₄(τ)(E₈(ζ)W(ζ) - 1)`,

together with the elementary rearrangement `brMinus + Sh·br0 = (brMinus + br0) + (Sh - 1)·br0`.
The first and third terms of the identity and the two factors `Sh - 1`, `br0` are polynomially
bounded on the ball (the `BBdd` calculus of `TileDevBall/BallShape.lean`), while the middle term
factorises as `Λ(τ) · Az(ζ)` with

* `‖Λ(τ)‖ ≤ C (scale w)^N e^{π Im(S • w)}` (`lambBound`, from `Tile.TBM.lamb`), and
* `‖Az(ζ)‖ ≤ C ‖Ept ζ‖ = C e^{-π Im ζ}` (`azBound`),

and `Im ζ ≥ Im (S • w) - 29/20` on the ball makes the product polynomially bounded.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.Tile.KMinusSharpChain
import Submission.Work.Asymptotics.EtailE.Shapes
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.TileDevBall.BallShape
import Submission.Work.Asymptotics.TileDevBall.BallAtoms
import Submission.Work.Asymptotics.TileDevBall.kplusDev8Ball
import Submission.Work.Asymptotics.TileDevBall.azBound

set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileDevBall

open Work.Kernels
open Work.Asymptotics.Compact

/-! ## Elementary ball geometry -/

/-- `scale ζ ≤ 4 · scale w` on the tile ball. -/
lemma ball_scale_le {w ζ : ℍ} (h : Ball w ζ) : scale ζ ≤ 4 * scale w := by
  have h1 : (ζ.im)⁻¹ ≤ 1 / 3 := by
    rw [inv_le_iff_one_le_mul₀ ζ.im_pos]
    linarith [h.him]
  have h2 : ‖(ζ : ℂ)‖ ≤ (49 / 20) * scale w := h.norm_le_scaled
  have h3 : (1 : ℝ) ≤ scale w := h.one_le_scale
  show (1 : ℝ) + (ζ.im)⁻¹ + ‖(ζ : ℂ)‖ ≤ 4 * scale w
  nlinarith [h1, h2, h3]

/-! ## The bracket identity -/

/-- The bracket identity of the cusp expansion (`EtailE_KMinus8.lean`). -/
lemma br_add_br0_decomp (ℓ : LogLambdaData) (τ z : ℍ) :
    brMinus ℓ 8 τ z + br0 8 ℓ τ z
      = (-3456 : ℂ) * E4Fun τ * (E10Fun z * ℓ.L z - Xc ℓ z)
        + (-(Work.Residues.Lamb ℓ τ))
          * (E8Fun z * WFun z - E6Fun z * (UFun z ^ 2 - VFun z ^ 2))
        + (1728 : ℂ) * psi4 ℓ τ * (E8Fun z * WFun z - 1) := by
  rw [brMinus_eight, br0_8]
  simp only [Work.Residues.bracket8e, Work.Residues.Lamb, Xc, c1728]
  ring

/-! ## The atom bounds in the `BBdd` calculus -/

/-- `𝓛(ζ)` is polynomially bounded on the tile ball. -/
lemma LBdd (ℓ : LogLambdaData) : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => ℓ.L ζ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.Funnel24.norm_L_le ℓ
  refine ⟨4 * C, 1, by positivity, by norm_num, fun w ζ hw => ?_⟩
  have h1 := hb ζ (by linarith [hw.him])
  have h2 : ‖(ζ : ℂ)‖ ≤ (49 / 20) * scale w := hw.norm_le_scaled
  have h3 : (1 : ℝ) ≤ scale w := hw.one_le_scale
  have h4 : (1 : ℝ) + ‖(ζ : ℂ)‖ ≤ 4 * scale w := by
    nlinarith [h2, h3]
  simp only [Real.rpow_one, zero_mul, Real.exp_zero, mul_one]
  calc ‖ℓ.L ζ‖ ≤ C * (1 + ‖(ζ : ℂ)‖) := h1
    _ ≤ C * (4 * scale w) := mul_le_mul_of_nonneg_left h4 hC.le
    _ = 4 * C * scale w := by ring

/-- `W(ζ) = θ₀₁⁴(ζ)` is bounded on the tile ball. -/
lemma WBdd : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => WFun ζ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.Funnel24.norm_W_le
  refine ⟨C, 0, hC, le_rfl, fun w ζ hw => ?_⟩
  have h1 := hb ζ (by linarith [hw.him])
  simpa using h1

/-- `Xc(ζ) = πiζ + c` is polynomially bounded on the tile ball. -/
lemma XcBdd (ℓ : LogLambdaData) : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => Xc ℓ ζ) := by
  have h1 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => ((Real.pi : ℂ) * Complex.I) * (ζ : ℂ)) :=
    BBdd.const_mul _ zcoe
  have h2 : BBdd 0 0 (fun (_ : ℍ) (_ : ℍ) => cuspC ℓ) := BBdd.const _
  have h := h1.add h2
  refine BBdd.congr ?_ (by simpa using h)
  funext w ζ
  rw [Xc]

/-! ## The `Λ` bound -/

/-- `‖Λ ℓ (n +ᵥ w)‖ ≤ C (scale w)^N e^{π Im(S • w)}` on the tile ball. -/
lemma lambBound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ w : ℍ, w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ, (n = 1 ∨ n = -1) →
        ‖Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w)‖
          ≤ C * (scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Work.Asymptotics.Tile.TBM.lamb ℓ
  refine ⟨C * 3 ^ M, N + M, by positivity, by positivity, ?_⟩
  intro w hw n hn
  set t : ℝ := (ModularGroup.S • w).im + 1 with ht
  have htpos : 0 < t := by rw [ht]; linarith [hw.2]
  have hle : (ModularGroup.S • w).im + 1 ≤ t := le_of_eq ht.symm
  have h := hb w n (imagAxis t htpos) t hn hw rfl hle
  have hsimS : (ModularGroup.S • w).im ≤ scale w :=
    le_trans (im_le_coe_norm _) (EtailE.E_norm_S_le_scale w)
  have ht3 : 1 + t ≤ 3 * scale w := by
    rw [ht]; linarith [hsimS, one_le_scale w]
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have hsplit : (3 * scale w) ^ M = 3 ^ M * (scale w) ^ M :=
    Real.mul_rpow (by norm_num) (le_of_lt (scale_pos w))
  have hrpow : (1 + t) ^ M ≤ 3 ^ M * (scale w) ^ M := by
    rw [← hsplit]
    exact Real.rpow_le_rpow hpos.le ht3 hM
  have hexp0 : Real.exp (Real.pi * (ModularGroup.S • w).im - 0 * Real.pi * t)
      = Real.exp (Real.pi * (ModularGroup.S • w).im) := by
    rw [zero_mul, zero_mul, sub_zero]
  rw [hexp0] at h
  calc ‖Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w)‖
      ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (Real.pi * (ModularGroup.S • w).im) := h
    _ ≤ C * (scale w) ^ N * (3 ^ M * (scale w) ^ M)
          * Real.exp (Real.pi * (ModularGroup.S • w).im) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow
            (mul_nonneg hC.le (Real.rpow_nonneg (scale_pos w).le N))) (Real.exp_pos _).le
    _ = C * 3 ^ M * (scale w) ^ (N + M) * Real.exp (Real.pi * (ModularGroup.S • w).im) := by
        rw [Real.rpow_add (scale_pos w) N M]; ring

/-! ## The main deviation bound -/

/-- The deviation bound for `brMinus + Sh · br0` at the single integer `n = ±1`. -/
theorem bracket8Ball_aux (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w ζ : ℍ), Ball w ζ →
        ‖brMinus ℓ 8 ((n : ℝ) +ᵥ w) ζ + Sh ((n : ℝ) +ᵥ w) ζ * br0 8 ℓ ((n : ℝ) +ᵥ w) ζ‖
          ≤ C * (scale w) ^ N := by
  obtain ⟨CL, NL, hCL, hNL, hLamb⟩ := lambBound ℓ
  obtain ⟨CA, hCA, hAz⟩ := azBound
  have hLζ : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => ℓ.L ζ) := LBdd ℓ
  have hWζ : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => WFun ζ) := WBdd
  have hXc : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => Xc ℓ ζ) := XcBdd ℓ
  have hpsi4 : BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => psi4 ℓ ((n : ℝ) +ᵥ w)) :=
    BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_psi4 ℓ n hn)
  have hT1 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      (-3456 : ℂ) * E4Fun ((n : ℝ) +ᵥ w) * (E10Fun ζ * ℓ.L ζ - Xc ℓ ζ)) := by
    have h := (BBdd.const_mul ((-3456 : ℂ)) (tE4 n hn)).mul ((zE10.mul hLζ).sub hXc)
    refine BBdd.congr ?_ (by simpa using h)
    funext w ζ; ring
  have hT3 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      (1728 : ℂ) * psi4 ℓ ((n : ℝ) +ᵥ w) * (E8Fun ζ * WFun ζ - 1)) := by
    have hE8W : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E8Fun ζ * WFun ζ - 1) := by
      have h := (zE8.mul hWζ).sub (BBdd.const (1 : ℂ))
      refine BBdd.congr ?_ (by simpa using h)
      funext w ζ; ring
    have h := (BBdd.const_mul (1728 : ℂ) hpsi4).mul hE8W
    refine BBdd.congr ?_ (by simpa using h)
    funext w ζ; ring
  have hSh1 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => Sh ((n : ℝ) +ᵥ w) ζ - 1) := by
    have h1 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ ^ 3 - 1) := by
      simpa using (zE4cube.sub (BBdd.const (1 : ℂ)))
    have h2 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => DeltaFun ζ * jInvariantFun ((n : ℝ) +ᵥ w)) := by
      have h := (zDelta.mul (tj n hn)).reduce
        (show (-(2 * Real.pi) + 0) ≤ 0 by linarith [Real.pi_pos])
        (show (0 + 2 * Real.pi) + (-(2 * Real.pi) + 0) ≤ 0 by linarith [Real.pi_pos])
      simpa using h
    have h := h1.sub h2
    refine BBdd.congr ?_ (by simpa only [max_self] using h)
    funext w ζ; rw [Sh]; ring
  have hbr0 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => br0 8 ℓ ((n : ℝ) +ᵥ w) ζ) := by
    have h := (BBdd.const_mul (3456 : ℂ) ((tE4 n hn).mul hXc)).sub
      (BBdd.const_mul (1728 : ℂ) hpsi4)
    refine BBdd.congr ?_ (by simpa using h)
    funext w ζ; rw [br0_8]; ring
  have hBig : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      (-3456 : ℂ) * E4Fun ((n : ℝ) +ᵥ w) * (E10Fun ζ * ℓ.L ζ - Xc ℓ ζ)
      + (1728 : ℂ) * psi4 ℓ ((n : ℝ) +ᵥ w) * (E8Fun ζ * WFun ζ - 1)
      + (Sh ((n : ℝ) +ᵥ w) ζ - 1) * br0 8 ℓ ((n : ℝ) +ᵥ w) ζ) := by
    have h := (hT1.add hT3).add (hSh1.mul hbr0)
    simpa using h
  obtain ⟨C0, N0, hC0, hN0, hb0⟩ := BBdd.exists_bound_zero hBig
  refine ⟨C0 + CL * CA * Real.exp (Real.pi * (29 / 20)) + 1, max N0 NL, by positivity,
    le_max_of_le_left hN0, ?_⟩
  intro w ζ hw
  have hscale1 : (1 : ℝ) ≤ scale w := hw.one_le_scale
  have hspos : (0 : ℝ) < scale w := hw.scale_pos
  have hN0le : N0 ≤ max N0 NL := le_max_left _ _
  have hNLle : NL ≤ max N0 NL := le_max_right _ _
  have hrpow0 : (scale w) ^ N0 ≤ (scale w) ^ (max N0 NL) := rpow_mono_scale hN0le
  have hrpowL : (scale w) ^ NL ≤ (scale w) ^ (max N0 NL) := rpow_mono_scale hNLle
  have hge1 : (1 : ℝ) ≤ (scale w) ^ (max N0 NL) := Real.one_le_rpow hscale1 (le_trans hN0 hN0le)
  have hposN : (0 : ℝ) ≤ (scale w) ^ (max N0 NL) := Real.rpow_nonneg hspos.le _
  have hL := hLamb w hw.hw n hn
  have hAζ := hAz ζ (by linarith [hw.him])
  have hEpt : ‖Work.Residues.Ept ζ‖ = Real.exp (-(Real.pi * ζ.im)) := Work.Residues.norm_Ept ζ
  have him : (ModularGroup.S • w).im - 29 / 20 ≤ ζ.im := hw.im_ge
  have hexp : Real.exp (Real.pi * (ModularGroup.S • w).im) * ‖Work.Residues.Ept ζ‖
      ≤ Real.exp (Real.pi * (29 / 20)) := by
    rw [hEpt, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [Real.pi_pos]
  have hT2 : ‖(Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w))
        * (E8Fun ζ * WFun ζ - E6Fun ζ * (UFun ζ ^ 2 - VFun ζ ^ 2))‖
      ≤ CL * CA * Real.exp (Real.pi * (29 / 20)) * (scale w) ^ NL := by
    rw [norm_mul]
    refine le_trans (mul_le_mul hL hAζ (norm_nonneg _) (by positivity)) ?_
    calc (CL * (scale w) ^ NL
            * Real.exp (Real.pi * (ModularGroup.S • w).im)) * (CA * ‖Work.Residues.Ept ζ‖)
        = CL * CA * (scale w) ^ NL
            * (Real.exp (Real.pi * (ModularGroup.S • w).im) * ‖Work.Residues.Ept ζ‖) := by ring
      _ ≤ CL * CA * (scale w) ^ NL * Real.exp (Real.pi * (29 / 20)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = CL * CA * Real.exp (Real.pi * (29 / 20)) * (scale w) ^ NL := by ring
  have hid : brMinus ℓ 8 ((n : ℝ) +ᵥ w) ζ
        + Sh ((n : ℝ) +ᵥ w) ζ * br0 8 ℓ ((n : ℝ) +ᵥ w) ζ
      = (((-3456 : ℂ) * E4Fun ((n : ℝ) +ᵥ w) * (E10Fun ζ * ℓ.L ζ - Xc ℓ ζ)
          + (1728 : ℂ) * psi4 ℓ ((n : ℝ) +ᵥ w) * (E8Fun ζ * WFun ζ - 1)
          + (Sh ((n : ℝ) +ᵥ w) ζ - 1) * br0 8 ℓ ((n : ℝ) +ᵥ w) ζ)
        + (-(Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w)))
          * (E8Fun ζ * WFun ζ - E6Fun ζ * (UFun ζ ^ 2 - VFun ζ ^ 2))) := by
    rw [show brMinus ℓ 8 ((n : ℝ) +ᵥ w) ζ
          + Sh ((n : ℝ) +ᵥ w) ζ * br0 8 ℓ ((n : ℝ) +ᵥ w) ζ
        = (brMinus ℓ 8 ((n : ℝ) +ᵥ w) ζ + br0 8 ℓ ((n : ℝ) +ᵥ w) ζ)
          + (Sh ((n : ℝ) +ᵥ w) ζ - 1) * br0 8 ℓ ((n : ℝ) +ᵥ w) ζ from by ring,
      br_add_br0_decomp ℓ ((n : ℝ) +ᵥ w) ζ]
    ring
  rw [hid]
  refine le_trans (norm_add_le _ _) ?_
  have hmain : ‖(-3456 : ℂ) * E4Fun ((n : ℝ) +ᵥ w) * (E10Fun ζ * ℓ.L ζ - Xc ℓ ζ)
        + (1728 : ℂ) * psi4 ℓ ((n : ℝ) +ᵥ w) * (E8Fun ζ * WFun ζ - 1)
        + (Sh ((n : ℝ) +ᵥ w) ζ - 1) * br0 8 ℓ ((n : ℝ) +ᵥ w) ζ‖
      ≤ C0 * (scale w) ^ (max N0 NL) :=
    le_trans (hb0 w ζ hw) (le_mul_rpow_mono hscale1 le_rfl hN0le hC0.le)
  have hT2' : ‖(-(Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w)))
        * (E8Fun ζ * WFun ζ - E6Fun ζ * (UFun ζ ^ 2 - VFun ζ ^ 2))‖
      ≤ CL * CA * Real.exp (Real.pi * (29 / 20)) * (scale w) ^ (max N0 NL) := by
    rw [show (-(Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w)))
          * (E8Fun ζ * WFun ζ - E6Fun ζ * (UFun ζ ^ 2 - VFun ζ ^ 2))
        = -((Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w))
          * (E8Fun ζ * WFun ζ - E6Fun ζ * (UFun ζ ^ 2 - VFun ζ ^ 2))) from by ring, norm_neg]
    exact le_trans hT2 (le_mul_rpow_mono hscale1 le_rfl hNLle (by positivity))
  have hcomb : C0 * (scale w) ^ (max N0 NL)
        + CL * CA * Real.exp (Real.pi * (29 / 20)) * (scale w) ^ (max N0 NL)
      ≤ (C0 + CL * CA * Real.exp (Real.pi * (29 / 20)) + 1) * (scale w) ^ (max N0 NL) := by
    have h2 := mul_nonneg hC0.le hposN
    have h3 := mul_nonneg (by positivity : (0:ℝ) ≤ CL * CA * Real.exp (Real.pi * (29 / 20))) hposN
    nlinarith [hge1, h2, h3, hposN]
  linarith [hmain, hT2', hcomb]

/-! ## The target -/

set_option autoImplicit false in
theorem bracket8Ball (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane, ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          3 ≤ ζ.im →
          ‖Work.Asymptotics.Compact.brMinus ℓ 8 ((n : ℝ) +ᵥ w) ζ
            + Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * Work.Asymptotics.Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) ζ‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := bracket8Ball_aux ℓ 1 (Or.inl rfl)
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := bracket8Ball_aux ℓ (-1) (Or.inr rfl)
  refine ⟨max C1 C2 + 1, max N1 N2, by positivity, le_max_of_le_left hN1, ?_⟩
  intro w hw n hn ζ hball him
  have hB : Ball w ζ := ⟨hw, hball, him⟩
  rcases hn with h | h
  · subst h
    exact le_trans (h1 w ζ hB)
      (le_mul_rpow_mono hB.one_le_scale (by linarith [le_max_left C1 C2]) (le_max_left N1 N2)
        (le_of_lt hC1))
  · subst h
    exact le_trans (h2 w ζ hB)
      (le_mul_rpow_mono hB.one_le_scale (by linarith [le_max_right C1 C2]) (le_max_right N1 N2)
        (le_of_lt hC2))

end Work.Asymptotics.TileDevBall
