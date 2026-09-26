/-
# The plain polynomial window on `(0, scale w]`, with the far-window brick as an input

`Work.Asymptotics.SKEC.EpolyWindowE_of_pieces` (`SKEC/WindowE.lean`) reduces the plain window on

  `E = KEpsilon`, `0 < t ≤ scale w`,  `‖K^{(d)}(w, i t)‖ ≤ C (scale w)^N (1 + t)^M`

to two pieces: the *far* piece on `1 ≤ t ≤ Im (S • w) - 1` and the *strip* piece on
`Im (S • w) - 1 ≤ t ≤ Im (S • w) + 1`; the remaining sub-ranges `0 < t ≤ 1` (flatness,
`Work.Asymptotics.EFlat` from `Epoint_Kfun`) and `Im (S • w) + 1 ≤ t ≤ scale w`
(`Work.Asymptotics.EpolyWindowE_top`) are supplied internally.

The strip piece is **proved** and clean: it is `Work.Asymptotics.EWindow_pole`
(`Submission/Work/Asymptotics/EWindow_pole.lean`, the three-zeros/maximum-modulus argument on the
disc of radius `29/20`; note that the factor `1 + e^{2πt}` it carries in its docstring is not
needed — the interior estimate `Khat_window_bound` is polynomial in `scale`).  The far piece is
`Work.Asymptotics.EWindow_far`, whose proof reduces (via `Work.Asymptotics.EWindow_far_of`) to the
three numerator bounds `Xi8_low_bound`, `Xi24_low_bound`, `Ncusp_low_bound` and the divisor lower
bound `divisor_lower_lowIm`.

This file therefore isolates the *single* remaining input of the window as a hypothesis named
`hfar`, and assembles the plain window from it.  When the numerator bounds land (the fleet's
`Submission/Work/Asymptotics/EpolyWindowE_Ncusp.lean` supplies the `Ncusp` one), `hfar` is
`EWindow_far ℓ d hd` and the window — and with it `SKEC.ERegimes_of_window`, hence
`Work.Asymptotics.E_seminorm` — closes.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.SKEC.Defs
import Submission.Work.Asymptotics.SKEC.WindowE
import Submission.Work.Asymptotics.EWindow_pole
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

open Work.Kernels

/-- **The plain polynomial window on the two-unit strip around the pole height**, i.e.
`‖K(w, i t)‖ ≤ C (scale w)^N (1 + t)^M` for `Im (S • w) - 1 ≤ t ≤ Im (S • w) + 1`.

`Work.Asymptotics.EWindow_pole` states this with an extra factor `1 + Real.exp (2π t)`; that factor
is not needed: the interior estimate `Work.Asymptotics.Khat_window_bound` is already polynomial in
`scale`, and the `S`-transport `Kfun_S_smul` turns it into the bound below (this is the same proof,
with the final enlargement by `1 + e^{2πt}` dropped). -/
theorem EWindow_pole_plain (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon →
        (ModularGroup.S • w).im - 1 ≤ t → t ≤ (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
  obtain ⟨Cw, Nw, hCw, hNw, hwin⟩ := Khat_window_bound ℓ d hd
  have hd2 : ((d : ℤ) / 2) = ((d / 2 : ℕ) : ℤ) := by
    rcases hd with rfl | rfl <;> norm_num
  refine ⟨Cw * 3 ^ (d / 2) * 3 ^ Nw, Nw + ((d / 2 : ℕ) : ℝ), Nw + ((d / 2 : ℕ) : ℝ),
    by positivity, by positivity, by positivity, ?_⟩
  intro w t hw h1 h2
  have ht : 0 < t := by have h := hw.2; linarith
  have hτ : Funnel (ModularGroup.S • w) := S_smul_mem_funnel hw
  have hK := Kfun_S_smul ℓ d hd (ModularGroup.S • w) (Work.Kernels.imagAxis t ht)
  rw [S_smul_S_smul] at hK
  have hwin' := hwin (ModularGroup.S • w) t ht hτ h1 h2
  have hnormτ : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 3 * Work.Kernels.scale w :=
    le_trans (Work.Kernels.coe_norm_le_scale _) (scale_S_smul_le_of_mem_KEpsilon hw)
  have hsm : ‖((ModularGroup.S • w : ℍ) : ℂ) ^ ((d : ℤ) / 2)‖
      = ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ (d / 2) := by
    rw [norm_zpow, hd2, zpow_natCast]
  rw [Work.Kernels.Kaxis, dif_pos ht, hK, norm_mul, norm_neg, hsm]
  have hmain : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ (d / 2)
        * ‖Work.Kernels.Khat ℓ d (ModularGroup.S • w) (Work.Kernels.imagAxis t ht)‖
      ≤ Cw * 3 ^ (d / 2) * 3 ^ Nw
          * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)) := by
    calc ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ (d / 2)
          * ‖Work.Kernels.Khat ℓ d (ModularGroup.S • w) (Work.Kernels.imagAxis t ht)‖
        ≤ (3 * Work.Kernels.scale w) ^ (d / 2)
            * (Cw * (Work.Kernels.scale (ModularGroup.S • w)) ^ Nw) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnormτ (d / 2)) hwin' (norm_nonneg _)
            (pow_nonneg (mul_nonneg (by norm_num) (Work.Kernels.scale_pos w).le) _)
      _ ≤ (3 * Work.Kernels.scale w) ^ (d / 2) * (Cw * (3 * Work.Kernels.scale w) ^ Nw) := by
          have h2' : (Work.Kernels.scale (ModularGroup.S • w)) ^ Nw
              ≤ (3 * Work.Kernels.scale w) ^ Nw :=
            Real.rpow_le_rpow (Work.Kernels.scale_pos _).le
              (scale_S_smul_le_of_mem_KEpsilon hw) hNw
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2' hCw.le)
            (pow_nonneg (mul_nonneg (by norm_num) (Work.Kernels.scale_pos w).le) _)
      _ = Cw * 3 ^ (d / 2) * 3 ^ Nw
            * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)) := by
          have hx : (Work.Kernels.scale w) ^ (d / 2) * (Work.Kernels.scale w) ^ Nw
              = (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast (Work.Kernels.scale w) (d / 2),
              ← Real.rpow_add (Work.Kernels.scale_pos w)]
            congr 1
            ring
          rw [mul_pow, Real.mul_rpow (by norm_num) (Work.Kernels.scale_pos w).le]
          rw [show 3 ^ (d / 2) * (Work.Kernels.scale w) ^ (d / 2)
                * (Cw * (3 ^ Nw * (Work.Kernels.scale w) ^ Nw))
              = (3 ^ (d / 2) * 3 ^ Nw * Cw)
                * ((Work.Kernels.scale w) ^ (d / 2) * (Work.Kernels.scale w) ^ Nw) by ring]
          rw [hx]
          ring
  refine le_trans hmain ?_
  have hle1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hM1 : (1 : ℝ) ≤ (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow hle1 (by linarith [hNw])
  calc Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ))
      ≤ Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ))
          * (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)) := by
        have h0 : (0 : ℝ) ≤ Cw * 3 ^ (d / 2) * 3 ^ Nw
            * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)) :=
          mul_nonneg (mul_nonneg (mul_nonneg hCw.le (by positivity)) (by positivity))
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
        calc Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ))
            = (Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)))
                * 1 := by ring
          _ ≤ _ * (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hM1 h0
    _ = Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ))
          * (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)) := by ring

/-- **The far-window hypothesis** (the statement of `Work.Asymptotics.EWindow_far`): the plain
window on `1 ≤ t ≤ Im (S • w) - 1`. -/
def FarWindow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon → 1 ≤ t →
      t ≤ (ModularGroup.S • w).im - 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M

/-- **The plain polynomial window on `E` up to `scale w`**, from the far-window hypothesis and the
(proved, clean) strip bound `Work.Asymptotics.EWindow_pole`. -/
theorem EpolyWindowE_of_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hfar : FarWindow ℓ d) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon → 0 < t →
        t ≤ Work.Kernels.scale w →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M :=
  EpolyWindowE_of_pieces ℓ d hd hfar (EWindow_pole_plain ℓ d hd)

end Work.Asymptotics
