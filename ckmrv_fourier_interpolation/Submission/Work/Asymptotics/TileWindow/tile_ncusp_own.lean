/-
# The tile bound for the cleared cusp numerator `Ncusp` with the exponent exposed

The principal-part window on the cusp-`±1` tiles needs the bound

  `‖Ncusp ℓ d (n +ᵥ w) z‖ ≤ C (scale w)^N (1 + e^{c (A - Im z)})`,  `A = Im (S • w)`, `c < 2π`,

for `w ∈ E = KEpsilon`, `n = ±1` and `Im z ≥ 1` (the `hNc` input of the cone-separated socket
`Work.Asymptotics.offspike_bound_general`).  The *proved* chain
`Tile.Ncusp_tile_crude → Tile.Ncusp_tile_sharp` gives this only in the form
`C (scale w)^N e^{c' A} e^{-π Im z}` with the *existential* constant `c' = max 0 (2π - δ)`,
where `δ` is the (also existential) exponent of the `ψ₄E₈ - ψ₂E₁₀` tile bound.  Since
`c' ≥ π` would make the comparison with `(1 + e^{c(A - Im z)})` fail for `Im z ≥ A`, the value of
`c'` must be *known*: it is `π`, because the tile bound `δ` is exactly `π` (`psi_combo_small`,
whose proof constructs `δ = Real.pi`).  The result is made visible here by re-deriving the two
steps with the exponent exposed:

* `psi_combo_bound_pi` — the `ψ₄E₈ - ψ₂E₁₀` tile bound with `δ = π` in the *type*;
* `Ncusp_tile_crude_param` — the crude `Ncusp` bound with the exponent `2π - δ` as an explicit
  parameter (a copy of `Tile.Ncusp_tile_crude` with `max 0 (2π - δ)` replaced by `2π - δ`);
* `Ncusp_tile_crude_pi` / `Ncusp_tile_sharp_pi` — the two steps at `δ = π`, again with the
  exponent exposed (copies of `Tile.Ncusp_tile_crude`/`Tile.Ncusp_tile_sharp`);
* `tile_ncusp_own` — the bound in the required shape, with `c = π`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.KMinusFunnelSlash
import Submission.Work.Asymptotics.mdiff_eta
import Submission.Work.Asymptotics.Tile.psi_combo_small
import Submission.Work.Asymptotics.Tile.Ncusp_tile_crude
import Submission.Work.Asymptotics.TileCone.Basic
import Submission.Work.Asymptotics.tile_KMinus_pp_aux
import Submission.Work.Asymptotics.tile_divisor_lower_cone
import Submission.Work.Asymptotics.tileXi_poly
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul

set_option maxHeartbeats 8000000

namespace Work.Asymptotics.TileWindow

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Asymptotics.Tile

noncomputable section

/-- The tile bound for `psiCombo = ψ₄E₈ - ψ₂E₁₀` with the exponent `δ = π` **exposed**
(so that the consumer can compute `2π - δ`). -/
theorem psi_combo_bound_pi (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)
          - Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)‖
        ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (-(Real.pi * (ModularGroup.S • w).im)) := by
  obtain ⟨CZ, NZ, hCZ, hNZ, hZb⟩ := Work.Asymptotics.EtailE.E_bdd_psi4E8_sub ℓ
  obtain ⟨CX, NX, hCX, hNX, hXb⟩ := E_bdd_Xfun
  have hCpos : (0 : ℝ) < CZ + Real.pi * CX := by
    have := mul_pos Real.pi_pos hCX
    linarith
  refine ⟨CZ + Real.pi * CX, max NZ NX, hCpos, le_max_of_le_left hNZ,
    fun w n hn hw => ?_⟩
  have hSnn : 0 ≤ (ModularGroup.S • w).im := Work.Asymptotics.EtailE.E_im_S_nonneg hw
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hZbw : ‖psiCombo ℓ w‖ ≤ CZ * (Work.Kernels.scale w) ^ NZ
      * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := hZb w hw
  have hXbw : ‖Work.Residues.Xfun w‖ ≤ CX * (Work.Kernels.scale w) ^ NX
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := hXb w hw
  have hexpZ : Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im)
      ≤ Real.exp ((-Real.pi) * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (by nlinarith [hSnn, Real.pi_pos])
  have hZ' : ‖psiCombo ℓ w‖ ≤ CZ * (Work.Kernels.scale w) ^ (max NZ NX)
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    refine le_trans hZbw ?_
    have h1 : CZ * (Work.Kernels.scale w) ^ NZ
        ≤ CZ * (Work.Kernels.scale w) ^ (max NZ NX) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_left _ _)) hCZ.le
    exact mul_le_mul h1 hexpZ (Real.exp_pos _).le
      (mul_nonneg hCZ.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
  have hX' : ‖Work.Residues.Xfun w‖ ≤ CX * (Work.Kernels.scale w) ^ (max NZ NX)
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    refine le_trans hXbw ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_right _ _)) hCX.le)
      (Real.exp_pos _).le
  have hcoc : psiCombo ℓ ((n : ℝ) +ᵥ w)
      = psiCombo ℓ w + (n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w) := by
    rcases hn with h | h
    · rw [h]; push_cast; rw [one_mul]; exact psiCombo_vadd_one ℓ w
    · rw [h]; push_cast; rw [neg_one_mul]; exact psiCombo_vadd_neg_one ℓ w
  have hcn : ‖(n : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]; rcases hn with h | h <;> rw [h] <;> norm_num
  have hk : ‖(n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖
      = Real.pi * ‖Work.Residues.Xfun w‖ := by
    rw [norm_mul, norm_mul, norm_mul, hcn, one_mul, Complex.norm_I, mul_one,
      Work.Asymptotics.EtailE.norm_pi]
  have h2 : Real.pi * ‖Work.Residues.Xfun w‖
      ≤ Real.pi * (CX * (Work.Kernels.scale w) ^ (max NZ NX)
          * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)) :=
    mul_le_mul_of_nonneg_left hX' Real.pi_pos.le
  have h3 : ‖psiCombo ℓ w‖ + Real.pi * ‖Work.Residues.Xfun w‖
      ≤ (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
        * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    have h4 : CZ * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
          + Real.pi * (CX * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im))
        = (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by ring
    exact le_trans (add_le_add hZ' h2) (le_of_eq h4)
  have hstep1 : ‖psiCombo ℓ ((n : ℝ) +ᵥ w)‖
      = ‖psiCombo ℓ w + (n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖ := by
    rw [hcoc]
  have hstep2 : ‖psiCombo ℓ w + (n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖
      ≤ ‖psiCombo ℓ w‖ + Real.pi * ‖Work.Residues.Xfun w‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [hk]
  have hstep4 : (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
        * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
      = (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
        * Real.exp (-(Real.pi * (ModularGroup.S • w).im)) := by
    rw [neg_mul]
  exact le_trans (le_of_eq hstep1) (le_trans hstep2 (le_trans h3 (le_of_eq hstep4)))

theorem Ncusp_tile_crude_param (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2 * Real.pi)
    (hF : ∃ CF NF : ℝ, 0 < CF ∧ 0 ≤ NF ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)
          - Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)‖
        ≤ CF * (Work.Kernels.scale w) ^ NF * Real.exp (-(δ * (ModularGroup.S • w).im))) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ z : UpperHalfPlane, 1 ≤ z.im →
          ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
            ≤ C * (Work.Kernels.scale w) ^ N * Real.exp ((2 * Real.pi - δ) * (ModularGroup.S • w).im)
                * Real.exp (Real.pi * z.im) := by
  obtain ⟨CF, NF, hCF, hNF, hFb⟩ := hF
  obtain ⟨CT, NT, hCT, hNT, hT⟩ := tile_tau_atoms ℓ
  obtain ⟨CZ, hCZ, hE4z, hE6z, hE8z, hE10z, hE14z, hUz, hWz, hVz, hUWz, hLSz,
    hDinvz, hjz, hE14dz, hE10dz⟩ := z_atoms ℓ
  -- the `τ`-atoms at the tiles
  have hE4T : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.E4Fun ((n : ℝ) +ᵥ w)‖ ≤ CT * (Work.Kernels.scale w) ^ NT :=
    fun w n hn hw => (hT w n hn hw).1
  have hE8T : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)‖ ≤ CT * (Work.Kernels.scale w) ^ NT :=
    fun w n hn hw => (hT w n hn hw).2.2.1
  have hDelT : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)‖ ≤ CT * (Work.Kernels.scale w) ^ NT :=
    fun w n hn hw => (hT w n hn hw).2.2.2.2.1
  have hpsi4T : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)‖ ≤ CT * (Work.Kernels.scale w) ^ NT :=
    fun w n hn hw => (hT w n hn hw).2.2.2.2.2.2.1
  have hDinvT : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖(Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w))⁻¹‖
        ≤ CT * (Work.Kernels.scale w) ^ NT * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
    fun w n hn hw => (hT w n hn hw).2.2.2.2.2.2.2.1
  have hjT : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)‖
        ≤ CT * (Work.Kernels.scale w) ^ NT * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
    fun w n hn hw => (hT w n hn hw).2.2.2.2.2.2.2.2
  -- `j · Δ` is moderate
  have hjD : Work.Asymptotics.EtailE.Bdd 0
      (fun w : ℍ => Work.Kernels.jInvariantFun w * Work.Kernels.DeltaFun w) :=
    Work.Asymptotics.EtailE.Bdd.mono (c := 2 * Real.pi + -(2 * Real.pi)) (c' := 0)
      (by linarith [Real.pi_pos])
      ((Work.Asymptotics.EtailE.E_bdd_j).mul Work.Asymptotics.EtailE.E_bdd_Delta)
  obtain ⟨CjD, NjD, hCjD, hNjD, hjDb⟩ := hjD
  have hjDT : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) * Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)‖
        ≤ CjD * (Work.Kernels.scale w) ^ NjD := by
    intro w n hn hw
    have h := hjDb w hw
    have h1 : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
        = Work.Kernels.jInvariantFun w :=
      vadd_int_eq_self _ (fun τ => Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ) n hn w
    have h2 : Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w) = Work.Kernels.DeltaFun w :=
      vadd_int_eq_self _ (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ) n hn w
    rw [h1, h2]
    simpa only [zero_mul, Real.exp_zero, mul_one] using h
  -- `Sh` instances for the `τ`-atoms
  have sE4 : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.E4Fun τ) :=
    Sh.of_tau_atom hCT hNT hE4T
  have sE8 : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.E8Fun τ) :=
    Sh.of_tau_atom hCT hNT hE8T
  have sDel : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.DeltaFun τ) :=
    Sh.of_tau_atom hCT hNT hDelT
  have spsi4 : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.psi4 ℓ τ) :=
    Sh.of_tau_atom hCT hNT hpsi4T
  have sDeli : Sh (2 * Real.pi) 0 (fun τ (_ : ℍ) => (Work.Kernels.DeltaFun τ)⁻¹) :=
    Sh.of_tau_atom_exp hCT hNT hDinvT
  have sj : Sh (2 * Real.pi) 0 (fun τ (_ : ℍ) => Work.Kernels.jInvariantFun τ) :=
    Sh.of_tau_atom_exp hCT hNT hjT
  have sjDel : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ) :=
    Sh.of_tau_atom hCjD hNjD hjDT
  have sF : Sh (-δ) 0 (fun τ (_ : ℍ) =>
      Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) := by
    refine ⟨CF, NF, hCF, hNF, fun w n z hn hw hz => ?_⟩
    simpa only [zero_mul, add_zero, neg_mul] using hFb w n hn hw
  -- `Sh` instances for the `z`-atoms
  have zE6 : Sh 0 0 (fun (_ : ℍ) z => Work.Kernels.E6Fun z) := Sh.of_zatom hCZ hE6z
  have zE8 : Sh 0 0 (fun (_ : ℍ) z => Work.Kernels.E8Fun z) := Sh.of_zatom hCZ hE8z
  have zE10 : Sh 0 0 (fun (_ : ℍ) z => Work.Kernels.E10Fun z) := Sh.of_zatom hCZ hE10z
  have zV : Sh 0 (-Real.pi) (fun (_ : ℍ) z => Work.Kernels.VFun z) :=
    Sh.of_zatom_exp hCZ (fun z hz => by simpa only [neg_mul] using hVz z hz)
  have zUW : Sh 0 (-Real.pi) (fun (_ : ℍ) z => Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2) :=
    Sh.of_zatom_exp hCZ (fun z hz => by simpa only [neg_mul] using hUWz z hz)
  have zLS : Sh 0 (-Real.pi) (fun (_ : ℍ) z => ℓ.L_S z) :=
    Sh.of_zatom_exp hCZ (fun z hz => by simpa only [neg_mul] using hLSz z hz)
  have zDinv : Sh 0 (2 * Real.pi) (fun (_ : ℍ) z => (Work.Kernels.DeltaFun z)⁻¹) :=
    Sh.of_zatom_exp hCZ hDinvz
  have zj : Sh 0 (2 * Real.pi) (fun (_ : ℍ) z => Work.Kernels.jInvariantFun z) :=
    Sh.of_zatom_exp hCZ hjz
  have zE14d : Sh 0 (2 * Real.pi) (fun (_ : ℍ) z => Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) :=
    Sh.of_zatom_exp hCZ hE14dz
  have zE10d : Sh 0 (2 * Real.pi) (fun (_ : ℍ) z => Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z) :=
    Sh.of_zatom_exp hCZ hE10dz
  -- the common exponents
  have hc0 : 0 ≤ 2 * Real.pi - δ := by linarith
  have hclt : 2 * Real.pi - δ < 2 * Real.pi := by linarith
  have hpi : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hmax2 : 2 * Real.pi - δ ≤ 2 * Real.pi - δ := le_refl _
  rcases hd with rfl | rfl
  · -- ## `d = 8`
    have hT8 : Sh ((2 * Real.pi - δ)) Real.pi (fun τ z => T8 ℓ τ z) := by
      have t1 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-3456) (sE4.mul (zE10.mul zLS))).mono (by linarith [hc0])
            (by linarith [Real.pi_pos]))
      have t2 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (Work.Kernels.E8Fun z * Work.Kernels.VFun z
                + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
              * (Work.Kernels.E4Fun τ
                * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
                / Work.Kernels.DeltaFun τ)) := by
        refine Sh.congr (fun τ z => by ring) (((zE8.mul zV).add (zE6.mul zUW)).mul
          ((sE4.mul sF).div sDeli) |>.mono ?_ (by linarith [Real.pi_pos]))
        linarith [hmax2]
      have t3 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z
              * Work.Kernels.VFun z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-1728) ((spsi4.mul zE8).mul zV)).mono (by linarith [hc0])
            (by linarith [Real.pi_pos]))
      exact Sh.congr (fun τ z => by rw [T8_cancelled ℓ τ z]; ring) (t1.add (t2.add t3))
    have hN : Sh ((2 * Real.pi - δ)) Real.pi (fun τ z => Ncusp ℓ 8 τ z) :=
      Sh.congr (fun τ z => Ncusp_eight_expansion ℓ τ z)
        (Sh.const_mul ((2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) hT8)
    obtain ⟨C, N, hC, hNn, hle⟩ := hN
    refine ⟨C, N, hC, hNn, fun w n hn hw z hz => ?_⟩
    refine le_trans (hle w n z hn hw hz) (le_of_eq ?_)
    rw [Real.exp_add]; ring
  · -- ## `d = 24`
    have hT24 : Sh ((2 * Real.pi - δ)) Real.pi (fun τ z => T24 ℓ τ z) := by
      have u1 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (-3456 : ℂ) * Work.Kernels.DeltaFun τ
              * (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L_S z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-3456) ((sDel.mul zE14d).mul zLS)).mono (by linarith [hc0])
            (by linarith [Real.pi_pos]))
      have u2 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (3456 : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ
              * Work.Kernels.VFun z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul 3456 (sjDel.mul zV)).mono (by linarith [hc0]) (by linarith [Real.pi_pos]))
      have u3 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (-3456 : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun z
              * Work.Kernels.VFun z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-3456) (sDel.mul (zj.mul zV))).mono (by linarith [hc0]) (by linarith [Real.pi_pos]))
      have u4 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (2 : ℂ)
              * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
                  * Work.Kernels.jInvariantFun τ) * Work.Kernels.VFun z) := by
        refine Sh.congr (fun τ z => by ring)
          ((Sh.const_mul 2 ((sF.mul sj).mul zV)).mono ?_ (by linarith [Real.pi_pos]))
        linarith [hmax2]
      have u5 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (-2 : ℂ)
              * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
                  * Work.Kernels.jInvariantFun z) * Work.Kernels.VFun z) := by
        refine Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-2) ((sF.mul zj).mul zV)).mono ?_ (by linarith [Real.pi_pos]))
        have h2 : (-δ : ℝ) ≤ (2 * Real.pi - δ) := by linarith [hc0, hδ]
        linarith
      have u6 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * Work.Kernels.jInvariantFun τ * Work.Kernels.VFun z) := by
        refine Sh.congr (fun τ z => by ring)
          (((sF.mul sj).mul zV).mono ?_ (by linarith [Real.pi_pos]))
        linarith [hmax2]
      have u7 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ
              * (Work.Kernels.E8Fun τ * Work.Kernels.VFun z)) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-1728) (spsi4.mul (sE8.mul zV))).mono (by linarith [hc0])
            (by linarith [Real.pi_pos]))
      have u8 : Sh ((2 * Real.pi - δ)) Real.pi
          (fun τ z => (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
              * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)) := by
        refine Sh.congr (fun τ z => by ring)
          ((sF.mul (zE10d.mul zUW)).mono ?_ (by linarith [Real.pi_pos]))
        have h2 : (-δ : ℝ) ≤ (2 * Real.pi - δ) := by linarith [hc0, hδ]
        linarith
      exact Sh.congr (fun τ z => by rw [T24_cancelled ℓ τ z]; ring)
        (Sh.add (Sh.add (Sh.add (Sh.add (Sh.add (Sh.add (Sh.add u1 u2) u3) u4) u5) u6)
          u7) u8)
    have hN : Sh ((2 * Real.pi - δ)) Real.pi (fun τ z => Ncusp ℓ 24 τ z) :=
      Sh.congr (fun τ z => Ncusp_twentyfour_expansion ℓ τ z)
        (Sh.const_mul ((2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) hT24)
    obtain ⟨C, N, hC, hNn, hle⟩ := hN
    refine ⟨C, N, hC, hNn, fun w n hn hw z hz => ?_⟩
    refine le_trans (hle w n z hn hw hz) (le_of_eq ?_)
    rw [Real.exp_add]; ring

/-- The crude tile bound for `Ncusp` with the exponent `2π - δ` evaluated at `δ = π`. -/
theorem Ncusp_tile_crude_pi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ z : UpperHalfPlane, 1 ≤ z.im →
          ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
            ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im)
                * Real.exp (Real.pi * z.im) := by
  obtain ⟨C, N, hC, hN, hbd⟩ :=
    Ncusp_tile_crude_param ℓ d hd (δ := Real.pi) Real.pi_pos
      (by linarith [Real.pi_pos]) (psi_combo_bound_pi ℓ)
  refine ⟨C, N, hC, hN, fun w n hn hw z hz => ?_⟩
  refine le_trans (hbd w n hn hw z hz) (le_of_eq ?_)
  rw [show (2 * Real.pi - Real.pi) = Real.pi by ring]

/-- The Schwarz upgrade of the crude tile bound for `Ncusp`, with the exponent
`exp(π · Im (S • w))` **exposed** (the constant `π` is exactly the `c` of
`Ncusp_tile_crude_pi`). -/
theorem Ncusp_tile_sharp_pi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hcrude : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ z : UpperHalfPlane, 1 ≤ z.im →
          ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
            ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im)
                * Real.exp (Real.pi * z.im)) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ z : UpperHalfPlane, 1 ≤ z.im →
          ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
            ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im)
                * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hcrude
  have hCpos : 0 < C * Real.exp (2 * Real.pi) + 1 := by
    have h := Real.exp_pos (2 * Real.pi)
    nlinarith [h, hC]
  refine ⟨C * Real.exp (2 * Real.pi) + 1, N, hCpos, hN,
    fun w n hn hw z hz => ?_⟩
  set B : ℝ := C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (mul_nonneg hC.le
      (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N)) (Real.exp_nonneg _)
  have hE1 : Real.exp (-(Real.pi * z.im)) * Real.exp (Real.pi * z.im) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hBbound : ∀ ζ : UpperHalfPlane, 1 ≤ ζ.im →
      ‖Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ‖ ≤ B := by
    intro ζ hζ
    rw [norm_mul, Work.Asymptotics.norm_Ecusp, hB]
    have h := hb w n hn hw ζ hζ
    have he1 : Real.exp (-(Real.pi * ζ.im)) * Real.exp (Real.pi * ζ.im) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc Real.exp (-(Real.pi * ζ.im)) * ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ‖
        ≤ Real.exp (-(Real.pi * ζ.im))
            * (C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im)
                * Real.exp (Real.pi * ζ.im)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
      _ = C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im)
            * (Real.exp (-(Real.pi * ζ.im)) * Real.exp (Real.pi * ζ.im)) := by ring
      _ = C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im) := by
          rw [he1, mul_one]
  have hper : ∀ ζ : UpperHalfPlane,
      (fun ζ : UpperHalfPlane =>
          Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ)
        ((1 : ℝ) +ᵥ ζ)
      = (fun ζ : UpperHalfPlane =>
          Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ) ζ := by
    intro ζ
    simp only [Work.Asymptotics.Ecusp_vadd_one, Work.Asymptotics.Ncusp_vadd_one]
    ring
  have hmd : MDiff (fun ζ : UpperHalfPlane =>
      Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ) :=
    (UpperHalfPlane.mdifferentiable_iff).mpr (Work.Asymptotics.mdiff_eta ℓ d ((n : ℝ) +ᵥ w))
  have hsh := Work.Asymptotics.periodic_zero_cusp_decay_uhp (f := fun ζ : UpperHalfPlane =>
      Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ)
    hB0 hper hmd hBbound (Work.Asymptotics.KMinusCuspBallLimit ℓ d hd ((n : ℝ) +ᵥ w)) z hz
  rw [norm_mul, Work.Asymptotics.norm_Ecusp] at hsh
  have hNc : ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
      ≤ Real.exp (Real.pi * z.im)
        * (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im))) := by
    calc ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
        = Real.exp (Real.pi * z.im)
            * (Real.exp (-(Real.pi * z.im)) * ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (Real.pi * z.im)
            * (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im))) :=
          mul_le_mul_of_nonneg_left hsh (Real.exp_nonneg _)
  have hexp : Real.exp (Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im))
      = Real.exp (-(Real.pi * z.im)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey : Real.exp (Real.pi * z.im)
        * (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im)))
      = (C * Real.exp (2 * Real.pi) * (Work.Kernels.scale w) ^ N
          * Real.exp (Real.pi * (ModularGroup.S • w).im)) * Real.exp (-(Real.pi * z.im)) := by
    rw [hB, show Real.exp (Real.pi * z.im)
          * ((C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im))
              * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im)))
        = (C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im))
          * (Real.exp (Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im)))
          * Real.exp (2 * Real.pi) from by ring,
      hexp]
    ring
  have hmono : (C * Real.exp (2 * Real.pi) * (Work.Kernels.scale w) ^ N
        * Real.exp (Real.pi * (ModularGroup.S • w).im)) * Real.exp (-(Real.pi * z.im))
      ≤ ((C * Real.exp (2 * Real.pi) + 1) * (Work.Kernels.scale w) ^ N
          * Real.exp (Real.pi * (ModularGroup.S • w).im)) * Real.exp (-(Real.pi * z.im)) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    have h2 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im) :=
      mul_nonneg (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N) (Real.exp_nonneg _)
    nlinarith [h2, Real.exp_pos (2 * Real.pi), hC.le]
  exact le_trans hNc (le_trans (le_of_eq hkey) hmono)

/-- **The `Ncusp` bound needed by the tile principal-part window** (`hNc` of the
`offspike` socket): on the cusp-`±1` tiles `Ncusp` is bounded by `C (scale w)^N (1 + e^{c(A - Im z)})`
with `A = Im (S • w)` and `c = π < 2π`. -/
theorem tile_ncusp_pi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im))) := by
  obtain ⟨C, N, hC, hN, hbd⟩ := Ncusp_tile_sharp_pi ℓ d hd (Ncusp_tile_crude_pi ℓ d hd)
  refine ⟨C, N, hC, hN, ?_⟩
  intro w hw n hn z hz
  refine le_trans (hbd w n hn hw z hz) ?_
  have hA : Real.exp (Real.pi * (ModularGroup.S • w).im)
      * Real.exp (-(Real.pi * z.im))
      = Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im))
      ≤ 1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im)) := by linarith
  have hsc : (0 : ℝ) ≤ C * (Work.Kernels.scale w) ^ N :=
    mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N)
  rw [show C * (Work.Kernels.scale w) ^ N * Real.exp (Real.pi * (ModularGroup.S • w).im)
        * Real.exp (-(Real.pi * z.im))
      = C * (Work.Kernels.scale w) ^ N
        * (Real.exp (Real.pi * (ModularGroup.S • w).im) * Real.exp (-(Real.pi * z.im))) from by ring,
    hA]
  exact mul_le_mul_of_nonneg_left h1 hsc

/-- The same bound in the `∃ c` form used by the cone-separated socket. -/
theorem tile_ncusp_own (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ c C N : ℝ, 0 ≤ c ∧ c < 2 * Real.pi ∧ 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (c * ((ModularGroup.S • w).im - z.im))) := by
  obtain ⟨C, N, hC, hN, hbd⟩ := tile_ncusp_pi ℓ d hd
  exact ⟨Real.pi, C, N, Real.pi_pos.le, by linarith [Real.pi_pos], hC, hN, hbd⟩

end

end Work.Asymptotics.TileWindow
