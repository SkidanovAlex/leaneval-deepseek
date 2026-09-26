/-
# The atom inventory of the cusp-`±1` tiles in the `Bdd` calculus

The cusp-`±1` tiles `±1 + E` (`E = KEpsilon = S(𝔽)`) carry the coefficient functions
`Gcusp ℓ d i j` of the CKMRV cusp expansion (`Submission/Work/Asymptotics/GcuspDefs.lean`),
which are built out of the modular atoms `E₂, E₄, E₆, E₈, E₁₀, E₁₄, Δ` and the quasimodular
data `phiVec i`, `psi2 ℓ`, `psi4 ℓ`, together with the constant `cuspL ℓ`.

This file records every one of those atoms, *translated by `n = ±1`*, in the weight calculus
`Bdd c F = ∃ C N, 0 < C ∧ 0 ≤ N ∧ ∀ w ∈ E, ‖F w‖ ≤ C (scale w)^N e^{c Im (S • w)}` of
`Submission/Work/Asymptotics/EtailE/Shapes.lean`.  The `T`-invariant atoms (`E₂, E₄, E₆, E₈,
E₁₀, E₁₄, Δ`) are transported from the `E`-bounds of `EtailE/Atoms.lean` by
`Work.Asymptotics.Tile.vadd_int_eq_self`; `psi2, psi4` (not `T`-invariant) come from
`Tile.tile_tau_atoms`; and `phiVec` is bounded through its explicit description
`(τ, τE₂(τ) − 3i/π, τE₂(τ)² − 6iE₂(τ)/π)`.

The immediate consumer is the moderate-growth bound for the cusp-expansion coefficients
`Gcusp ℓ d i j (±1 + w)` (needed by the `layerTrunc`/`highPart` halves of the cusp-`±1` layer),
which is a finite combination of these atoms.
-/
import Mathlib
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.Tile.tile_tau_atoms
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.Tile.Ncusp_tile_crude

noncomputable section
open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm
namespace Work.Asymptotics
open Work.Kernels
open Work.Asymptotics.Tile (vadd_int_eq_self)
open Work.Asymptotics.EtailE (Bdd)

/-- A `T`-invariant `Bdd` function, translated. -/
lemma Bdd.shift {c : ℝ} {F : ℍ → ℂ} (h : Bdd c F) (hF : ∀ τ : ℍ, F ((1:ℝ)+ᵥτ) = F τ)
    (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd c (fun w : ℍ => F ((n:ℝ)+ᵥw)) :=
  Bdd.congr ((funext (fun w => vadd_int_eq_self F hF n hn w)).symm) h

lemma Bdd.const' (d : ℂ) : Bdd 0 (fun _ : ℍ => d) :=
  Bdd.congr (funext (fun _ => by ring)) (Bdd.const_mul d (Bdd.one 0 le_rfl))

lemma Bdd.natCast (m : ℕ) : Bdd 0 (fun _ : ℍ => (m : ℂ)) := by
  simpa using Bdd.const' (m : ℂ)

/-- `w ↦ ‖w + n‖` moderate. -/
lemma Bdd.vadd (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd 0 (fun w : ℍ => (((n:ℝ)+ᵥw : ℍ) : ℂ)) := by
  refine ⟨2, 1, by norm_num, by norm_num, fun w _ => ?_⟩
  simp only [EtailE.exp_zero_im, mul_one, Real.rpow_one]
  have hn1 : ‖(((n:ℝ)) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases hn with h | h <;> rw [h] <;> norm_num
  have hw : ‖(w:ℂ)‖ ≤ scale w := by
    rw [Work.Kernels.scale]; linarith [inv_nonneg.mpr w.im_pos.le]
  calc ‖(((n:ℝ)+ᵥw : ℍ) : ℂ)‖ = ‖(((n:ℝ)) : ℂ) + (w:ℂ)‖ := by rw [UpperHalfPlane.coe_vadd]
    _ ≤ ‖(((n:ℝ)) : ℂ)‖ + ‖(w:ℂ)‖ := norm_add_le _ _
    _ = 1 + ‖(w:ℂ)‖ := by rw [hn1]
    _ ≤ 1 + scale w := add_le_add le_rfl hw
    _ ≤ 2 * scale w := by have := Work.Kernels.one_le_scale w; linarith

/-- `Bdd` for the shifted atoms. -/
lemma Bdd.vadd_E2 (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd 0 (fun w : ℍ => E2Fun ((n:ℝ)+ᵥw)) :=
  Bdd.shift EtailE.E_bdd_E2 (fun τ => E2Fun_vadd_one τ) n hn

lemma Bdd.vadd_E4 (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd 0 (fun w : ℍ => E4Fun ((n:ℝ)+ᵥw)) :=
  Bdd.shift EtailE.E_bdd_E4 (fun τ => KernelFacts.E4Fun_vadd_one τ) n hn

lemma Bdd.vadd_E6 (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd 0 (fun w : ℍ => E6Fun ((n:ℝ)+ᵥw)) :=
  Bdd.shift EtailE.E_bdd_E6 (fun τ => KernelFacts.E6Fun_vadd_one τ) n hn

lemma Bdd.vadd_E8 (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd 0 (fun w : ℍ => E8Fun ((n:ℝ)+ᵥw)) :=
  Bdd.shift EtailE.E_bdd_E8 (fun τ => KernelFacts.E8Fun_vadd_one τ) n hn

lemma Bdd.vadd_E10 (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd 0 (fun w : ℍ => E10Fun ((n:ℝ)+ᵥw)) :=
  Bdd.shift EtailE.E_bdd_E10 (fun τ => KernelFacts.E10Fun_vadd_one τ) n hn

lemma Bdd.vadd_E14 (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd 0 (fun w : ℍ => E14Fun ((n:ℝ)+ᵥw)) :=
  Bdd.shift EtailE.E_bdd_E14 (fun τ => KernelFacts.E14Fun_vadd_one τ) n hn

lemma Bdd.vadd_Delta (n : ℤ) (hn : n = 1 ∨ n = -1) : Bdd 0 (fun w : ℍ => DeltaFun ((n:ℝ)+ᵥw)) :=
  Bdd.mono (by linarith [Real.pi_pos])
    (Bdd.shift EtailE.E_bdd_Delta (fun τ => KernelFacts.DeltaFun_vadd_one τ) n hn)

lemma Bdd.vadd_psi2 (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd 0 (fun w : ℍ => psi2 ℓ ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Tile.tile_tau_atoms ℓ
  refine ⟨C, N, hC, hN, fun w hw => ?_⟩
  rw [EtailE.exp_zero_im, mul_one]
  exact (hb w n hn hw).2.2.2.2.2.1

lemma Bdd.vadd_psi4 (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd 0 (fun w : ℍ => psi4 ℓ ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Tile.tile_tau_atoms ℓ
  refine ⟨C, N, hC, hN, fun w hw => ?_⟩
  rw [EtailE.exp_zero_im, mul_one]
  exact (hb w n hn hw).2.2.2.2.2.2.1

lemma Bdd.vadd_phi0 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd 0 (fun w : ℍ => phiVec ((n:ℝ)+ᵥw) 0) := by
  refine Bdd.congr ?_ (Bdd.vadd n hn)
  funext w
  rfl

lemma Bdd.vadd_phi1 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd 0 (fun w : ℍ => phiVec ((n:ℝ)+ᵥw) 1) := by
  have h : Bdd 0 (fun w : ℍ => (((n:ℝ)+ᵥw : ℍ) : ℂ) * E2Fun ((n:ℝ)+ᵥw)
      - 3*Complex.I/(Real.pi:ℂ)) :=
    ((Bdd.vadd n hn).mul_zero (Bdd.vadd_E2 n hn)).sub (Bdd.const' (3*Complex.I/(Real.pi:ℂ)))
  refine Bdd.congr ?_ h
  funext w
  rfl

lemma Bdd.vadd_phi2 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd 0 (fun w : ℍ => phiVec ((n:ℝ)+ᵥw) 2) := by
  have h : Bdd 0 (fun w : ℍ => (((n:ℝ)+ᵥw : ℍ) : ℂ) * (E2Fun ((n:ℝ)+ᵥw) * E2Fun ((n:ℝ)+ᵥw))
      - (6*Complex.I/(Real.pi:ℂ)) * E2Fun ((n:ℝ)+ᵥw)) :=
    ((Bdd.vadd n hn).mul_zero ((Bdd.vadd_E2 n hn).mul_zero (Bdd.vadd_E2 n hn))).sub
      ((Bdd.const' (6*Complex.I/(Real.pi:ℂ))).mul_zero (Bdd.vadd_E2 n hn))
  refine Bdd.congr ?_ h
  funext w
  change (((n:ℝ)+ᵥw : ℍ) : ℂ) * (E2Fun ((n:ℝ)+ᵥw) * E2Fun ((n:ℝ)+ᵥw))
      - (6*Complex.I/(Real.pi:ℂ)) * E2Fun ((n:ℝ)+ᵥw) = phi2 ((n:ℝ)+ᵥw)
  rw [phi2]
  ring




end Work.Asymptotics
