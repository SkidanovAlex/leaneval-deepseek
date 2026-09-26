/-
# The tile principal-part Lipschitz bound (the `hLip` input of `tile_pp_window_core_of`)

For `w` in the cusp-`0` neighbourhood `E = KEpsilon` of `𝒟`, `n = ±1` and
`t ∈ [Im w / 2, 1]`, the CKMRV kernel `z ↦ K^{(d)}(n + w, z)` has at `z = w = (n+w) - n` a
simple pole of residue `n/(2π)` (`Work.Residues.hasResidue_Kfun_second_translate`), and the
target bounds its *holomorphic remainder*

  `‖K(n+w, i t) · (i t - w) - n/(2π)‖ ≤ C (scale w)^N ‖i t - w‖`

uniformly in `w ∈ E`, `n = ±1` and `t ∈ [Im w/2, 1]` (off the coincidence
`j (i t) = j (n + w)` and off the point `i t = w`).

## Contents of this file

* `tile_pp_uniform_lip_of` (**proved here**): the target follows from two tile-uniform inputs,
  split at the distance `‖i t - w‖ = Im w / 8` from the translate pole:

  * `hnear` — the *spike* (`‖i t - w‖ ≤ Im w / 8`): the Lipschitz bound itself, localised near
    the pole (where the naive bound on `K` alone is impossible, since `K` blows up there);
  * `hfar` — the *off-spike* (`Im w / 8 ≤ ‖i t - w‖`): a plain polynomial bound on the kernel,
    which suffices there because the principal part `(n/2π)/(i t - w)` is bounded by
    `(n/π)/(Im w/4)` in that regime.

The two inputs are proved in the companion files
`Submission/Work/Asymptotics/TileWindow/tile_pp_near.lean` (the spike) and
`Submission/Work/Asymptotics/TileWindow/tile_K_far.lean` (the off-spike).

Numerically (validated model of `K = (K₊ + K₋)/2` reproducing the machine-checked residues) the
supremum of the target's left-hand side over the window is attained at `t = 1` and equals
`5·y⁻⁴` (`d = 8`) resp. `0.53·y⁻¹²` (`d = 24`) for `w = i y`, so the exponent `N` is needed and
the statement is *not* uniform (the left-hand side is unbounded as `w → 0`).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Asymptotics.Tile.tileLayerDefs
import Submission.Work.Asymptotics.TileWindow.tile_K_cone_sep
import Submission.Work.Asymptotics.tilePPWindowSpike

namespace Work.Asymptotics.TileWindow

open UpperHalfPlane

/-- **The target from the two tile-uniform inputs** (spike / off-spike).

The split point is the distance `Im w / 8` from the translate pole `z = w`:
`‖i t - w‖ ≤ Im w/8` is the spike (input `hnear`, which is the target itself localised), and
`Im w/8 ≤ ‖i t - w‖` is the off-spike, where the kernel bound `hfar` together with
`‖i t - w‖ ≥ Im w/8 ≥ 1/(8 scale w)` controls both `K · (i t - w)` and the principal part. -/
theorem tile_pp_uniform_lip_of (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hnear : ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → ‖((t : ℂ) * Complex.I - (w : ℂ))‖ ≤ w.im / 8 →
        ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) ≠
          Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            * (((t : ℂ) * Complex.I) - (w : ℂ)) - (n : ℂ) / (2 * (Real.pi : ℂ))‖
          ≤ C * (Work.Kernels.scale w) ^ N * ‖((t : ℂ) * Complex.I - (w : ℂ))‖)
    (hfar : ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → w.im / 8 ≤ ‖((t : ℂ) * Complex.I - (w : ℂ))‖ →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) ≠
          Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            * (((t : ℂ) * Complex.I) - (w : ℂ)) - (n : ℂ) / (2 * (Real.pi : ℂ))‖
          ≤ C * (Work.Kernels.scale w) ^ N * ‖((t : ℂ) * Complex.I - (w : ℂ))‖ := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hnear⟩ := hnear
  obtain ⟨C₂, N₂, hC₂, hN₂, hfar⟩ := hfar
  have hM0 : (0 : ℝ) ≤ max C₂ (4 / Real.pi) := le_trans hC₂ (le_max_left _ _)
  have hCfar : (0 : ℝ) ≤ 2 * max C₂ (4 / Real.pi) + 1 := by linarith
  have hNfar : (0 : ℝ) ≤ max N₂ 1 := le_trans hN₂ (le_max_left _ _)
  refine ⟨max C₁ (2 * max C₂ (4 / Real.pi) + 1), max N₁ (max N₂ 1), ?_, ?_, ?_⟩
  · exact le_trans hC₁ (le_max_left _ _)
  · exact le_trans hN₁ (le_max_left _ _)
  intro w hw n hn t ht h1 h2 hzw hjne
  have hspos : 0 < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  set z : ℂ := (t : ℂ) * Complex.I - (w : ℂ) with hz
  have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) := by
    rw [Work.Kernels.Kaxis, dif_pos ht]
  -- the final shape, monotone in the constants and the exponent
  have hfinal : ∀ (C N : ℝ), 0 ≤ C → C ≤ max C₁ (2 * max C₂ (4 / Real.pi) + 1) →
      N ≤ max N₁ (max N₂ 1) →
      C * (Work.Kernels.scale w) ^ N * ‖z‖
        ≤ max C₁ (2 * max C₂ (4 / Real.pi) + 1) * (Work.Kernels.scale w) ^ (max N₁ (max N₂ 1))
          * ‖z‖ := by
    intro C N hC0 hC hN
    have h2' : (Work.Kernels.scale w) ^ N ≤ (Work.Kernels.scale w) ^ (max N₁ (max N₂ 1)) :=
      Real.rpow_le_rpow_of_exponent_le hs1 hN
    have h3' : C * (Work.Kernels.scale w) ^ N
        ≤ max C₁ (2 * max C₂ (4 / Real.pi) + 1)
            * (Work.Kernels.scale w) ^ (max N₁ (max N₂ 1)) :=
      calc C * (Work.Kernels.scale w) ^ N
          ≤ C * (Work.Kernels.scale w) ^ (max N₁ (max N₂ 1)) :=
            mul_le_mul_of_nonneg_left h2' hC0
        _ ≤ max C₁ (2 * max C₂ (4 / Real.pi) + 1)
              * (Work.Kernels.scale w) ^ (max N₁ (max N₂ 1)) :=
            mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hspos.le _)
    exact mul_le_mul_of_nonneg_right h3' (norm_nonneg z)
  by_cases hsmall : ‖z‖ ≤ w.im / 8
  · refine le_trans (hnear w hw n hn t ht h1 h2 hsmall hzw hjne) ?_
    exact hfinal C₁ N₁ hC₁ (le_max_left _ _) (le_max_left _ _)
  · -- off-spike: the kernel itself is polynomially bounded
    have hbig : w.im / 8 < ‖z‖ := not_le.mp hsmall
    have hfar' := hfar w hw n hn t ht h1 h2 (le_of_lt hbig)
    rw [hKax] at hfar'
    have hn1 : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
    have hpp : ‖(n : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, hn1]
      have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [h2pi]
    have hz8 : (1 / 8 : ℝ) ≤ Work.Kernels.scale w * ‖z‖ := by
      have hw8 : w.im / 8 ≤ ‖z‖ := le_of_lt hbig
      have hlt : (w.im)⁻¹ ≤ Work.Kernels.scale w := by
        simp only [Work.Kernels.scale]; linarith [norm_nonneg (w : ℂ)]
      have hprod : (w.im)⁻¹ * (w.im / 8) = 1 / 8 := by field_simp
      rw [← hprod]
      exact mul_le_mul hlt hw8 (by positivity) (by positivity)
    have hconst : (1 : ℝ) / (2 * Real.pi) ≤ (4 / Real.pi) * Work.Kernels.scale w * ‖z‖ := by
      have h4 : (1 : ℝ) / (2 * Real.pi) = (4 / Real.pi) * (1 / 8) := by field_simp; ring
      rw [h4]
      calc (4 / Real.pi) * (1 / 8) ≤ (4 / Real.pi) * (Work.Kernels.scale w * ‖z‖) :=
            mul_le_mul_of_nonneg_left hz8 (by positivity)
        _ = (4 / Real.pi) * Work.Kernels.scale w * ‖z‖ := by ring
    have hbound : ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) * z
          - (n : ℂ) / (2 * (Real.pi : ℂ))‖
        ≤ (C₂ * (Work.Kernels.scale w) ^ N₂ + 4 / Real.pi * Work.Kernels.scale w) * ‖z‖ := by
      calc ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) * z
            - (n : ℂ) / (2 * (Real.pi : ℂ))‖
          ≤ ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) * z‖
            + ‖(n : ℂ) / (2 * (Real.pi : ℂ))‖ := norm_sub_le _ _
        _ = ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ * ‖z‖
            + 1 / (2 * Real.pi) := by rw [norm_mul, hpp]
        _ ≤ C₂ * (Work.Kernels.scale w) ^ N₂ * ‖z‖
            + (4 / Real.pi) * Work.Kernels.scale w * ‖z‖ :=
              add_le_add (mul_le_mul_of_nonneg_right hfar' (norm_nonneg z)) hconst
        _ = (C₂ * (Work.Kernels.scale w) ^ N₂ + 4 / Real.pi * Work.Kernels.scale w) * ‖z‖ := by
              ring
    have hN2le : N₂ ≤ max N₂ 1 := le_max_left _ _
    have h1le : (1 : ℝ) ≤ max N₂ 1 := le_max_right _ _
    have hscaleN : (Work.Kernels.scale w) ^ N₂ ≤ (Work.Kernels.scale w) ^ (max N₂ 1) :=
      Real.rpow_le_rpow_of_exponent_le hs1 hN2le
    have hscale1 : (Work.Kernels.scale w : ℝ) ≤ (Work.Kernels.scale w) ^ (max N₂ 1) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hs1 h1le
    have hNpos : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N₂ 1) := Real.rpow_nonneg hspos.le _
    have h2 : C₂ * (Work.Kernels.scale w) ^ N₂
        ≤ max C₂ (4 / Real.pi) * (Work.Kernels.scale w) ^ (max N₂ 1) :=
      calc C₂ * (Work.Kernels.scale w) ^ N₂
          ≤ max C₂ (4 / Real.pi) * (Work.Kernels.scale w) ^ N₂ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hspos.le _)
        _ ≤ max C₂ (4 / Real.pi) * (Work.Kernels.scale w) ^ (max N₂ 1) :=
            mul_le_mul_of_nonneg_left hscaleN (le_trans hC₂ (le_max_left _ _))
    have h3 : (4 / Real.pi : ℝ) * Work.Kernels.scale w
        ≤ max C₂ (4 / Real.pi) * (Work.Kernels.scale w) ^ (max N₂ 1) :=
      calc (4 / Real.pi : ℝ) * Work.Kernels.scale w
          ≤ max C₂ (4 / Real.pi) * Work.Kernels.scale w :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hspos.le
        _ ≤ max C₂ (4 / Real.pi) * (Work.Kernels.scale w) ^ (max N₂ 1) :=
            mul_le_mul_of_nonneg_left hscale1 (by positivity)
    have hstep : C₂ * (Work.Kernels.scale w) ^ N₂ + 4 / Real.pi * Work.Kernels.scale w
        ≤ (2 * max C₂ (4 / Real.pi) + 1) * (Work.Kernels.scale w) ^ (max N₂ 1) := by
      nlinarith [h2, h3, hNpos]
    have hCf : (2 * max C₂ (4 / Real.pi) + 1)
        ≤ max C₁ (2 * max C₂ (4 / Real.pi) + 1) := le_max_right _ _
    have hNf : max N₂ 1 ≤ max N₁ (max N₂ 1) := le_max_right _ _
    have hscaleF : (Work.Kernels.scale w) ^ (max N₂ 1)
        ≤ (Work.Kernels.scale w) ^ (max N₁ (max N₂ 1)) :=
      Real.rpow_le_rpow_of_exponent_le hs1 hNf
    calc ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) * z
          - (n : ℂ) / (2 * (Real.pi : ℂ))‖
        ≤ (C₂ * (Work.Kernels.scale w) ^ N₂ + 4 / Real.pi * Work.Kernels.scale w) * ‖z‖ := hbound
      _ ≤ (2 * max C₂ (4 / Real.pi) + 1) * (Work.Kernels.scale w) ^ (max N₂ 1) * ‖z‖ :=
          mul_le_mul_of_nonneg_right hstep (norm_nonneg z)
      _ ≤ max C₁ (2 * max C₂ (4 / Real.pi) + 1)
            * (Work.Kernels.scale w) ^ (max N₁ (max N₂ 1)) * ‖z‖ :=
          hfinal (2 * max C₂ (4 / Real.pi) + 1) (max N₂ 1) hCfar hCf hNf


/-! ## The `T`-affinity of the tile kernel, and the reduction of the target to a single
explicit remainder

`Work.Residues.Kfun_T2` says `(T-I)² K = 0` in the first variable, i.e.
`K(τ+2,z) - 2K(τ+1,z) + K(τ,z) = 0`.  On the tiles `n +ᵥ w` (`n = ±1`, `w ∈ E`) this says that
the kernel is *affine* over the translates:

  `K(n +ᵥ w, z) = K(w, z) + n·D(w,z)`,   `D(w,z) := K(1 +ᵥ w, z) − K(w, z)`.

Since `z ↦ K(w,z)` has its poles at `z = w ± 1` (and *not* at `z = w`), the whole translate pole
`z = w = n +ᵥ w − n` is carried by the single difference `D`; the original `z ↦ K(n+ᵥw, z)` is
recovered from `z ↦ K(w,z)` and `D` alone.  With

  `E(w,z) := (z − w)·D(w,z) − 1/(2π)`

the identity gives the exact decomposition

  `K(n +ᵥ w, z)·(z − w) − n/(2π) = (z − w)·K(w,z) + n·E(w,z)`   (`n = ±1`),

so the assigned theorem follows from the (already proved, for `w ∈ E`, `t ≤ 1`) flatness of
`z ↦ K(w,z)` on the imaginary axis (`Work.Asymptotics.EFlat`, field `.1` of
`Work.Asymptotics.Epoint_Kfun`) together with the single explicit bound on `E`. -/

/-- **The `T`-affinity of the CKMRV kernel on the tiles.**  For `n = ±1`,
`K(n +ᵥ w, z) = K(w, z) + n·(K(1 +ᵥ w, z) − K(w, z))`. -/
theorem tile_Kfun_affine (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (w z : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) z
      = Work.Kernels.Kfun ℓ d w z
        + (n : ℝ) * (Work.Kernels.Kfun ℓ d ((1 : ℝ) +ᵥ w) z
            - Work.Kernels.Kfun ℓ d w z) := by
  rcases hn with rfl | rfl
  · norm_num
  · have h := congr_fun (Work.Residues.Kfun_T2 ℓ d hd z) ((-1 : ℝ) +ᵥ w)
    simp only [Work.Kernels.T2op, Pi.zero_apply] at h
    rw [← add_vadd, ← add_vadd] at h
    norm_num at h
    push_cast
    linear_combination h

/-- **Reduction of the assigned theorem to the flatness of `z ↦ K(w,z)` and one explicit
remainder.**

`hEFlat` is the *proved* flatness of the E-tile kernel on the lower window: it is
`Work.Asymptotics.EFlat ℓ d` (defined in `Submission/Work/Asymptotics/KEpsilon.lean`) at
`N = 0`, produced by the proved `Work.Asymptotics.Epoint_Kfun ℓ d hd` (its `.1` field):
`Epoint_Kfun ℓ d hd |>.1 0 (le_refl 0)`.
`hE` is the single remaining obligation, a bound on the explicit *entire* function
`E(w,z) = (z − w)(K(w + 1, z) − K(w, z)) − 1/(2π)`
(`E(w,w) = 0`; `E(w,·)` has poles only at `z = w ± 1`); no `n` occurs in it.
The hypothesis `i t ≠ w` is essential and must be kept: at `i t = w` Lean's totalised `Kfun`
returns the junk value `0` for BOTH kernels (the factor `(j τ − j z)⁻¹` carries `0⁻¹ = 0`), so
the value of the left-hand side there is the constant `1/(2π)` while the right-hand side vanishes.
It is the *only* excluded point: by `Work.Asymptotics.tile_window_coincidence_ne` the window meets
no other `j`-coincidence of `z ↦ Kfun ℓ d (1+ᵥw) z` or `z ↦ Kfun ℓ d w z`. -/
theorem tile_pp_uniform_lip_of_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hEFlat : ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (t : ℝ) (ht : 0 < t),
        t ≤ 1 →
        ‖Work.Kernels.Kfun ℓ d w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N)
    (hE : ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        ‖(Work.Kernels.Kfun ℓ d ((1 : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            - Work.Kernels.Kfun ℓ d w (Work.Kernels.imagAxis t ht))
            * (((t : ℂ) * Complex.I) - (w : ℂ)) - 1 / (2 * (Real.pi : ℂ))‖
          ≤ C * (Work.Kernels.scale w) ^ N * ‖((t : ℂ) * Complex.I - (w : ℂ))‖) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) ≠
          Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            * (((t : ℂ) * Complex.I) - (w : ℂ)) - (n : ℂ) / (2 * (Real.pi : ℂ))‖
          ≤ C * (Work.Kernels.scale w) ^ N * ‖((t : ℂ) * Complex.I - (w : ℂ))‖ := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hF⟩ := hEFlat
  obtain ⟨C₂, N₂, hC₂, hN₂, hE⟩ := hE
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, le_max_of_le_left hN₁, ?_⟩
  intro w hw n hn t ht h1 h2 hzw _
  set z : ℂ := (t : ℂ) * Complex.I - (w : ℂ) with hz
  set za : ℍ := Work.Kernels.imagAxis t ht with hza
  have hn1 : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
  have hC0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hspos : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hNmax1 : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hNmax2 : (Work.Kernels.scale w) ^ N₂ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hNpos : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) := Real.rpow_nonneg hspos.le _
  -- the exact decomposition
  have haff := tile_Kfun_affine ℓ d hd w za n hn
  have hkey : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) za * z - (n : ℂ) / (2 * (Real.pi : ℂ))
      = z * Work.Kernels.Kfun ℓ d w za
        + (n : ℂ) * ((Work.Kernels.Kfun ℓ d ((1 : ℝ) +ᵥ w) za
            - Work.Kernels.Kfun ℓ d w za) * z - 1 / (2 * (Real.pi : ℂ))) := by
    rw [haff]
    have hcast : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; ring
    rw [hcast]
    ring
  have hEval := hE w hw t ht h1 h2 hzw
  have hFval := hF w hw t ht h2
  calc ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) za * z - (n : ℂ) / (2 * (Real.pi : ℂ))‖
      = ‖z * Work.Kernels.Kfun ℓ d w za
          + (n : ℂ) * ((Work.Kernels.Kfun ℓ d ((1 : ℝ) +ᵥ w) za
              - Work.Kernels.Kfun ℓ d w za) * z - 1 / (2 * (Real.pi : ℂ)))‖ := by rw [hkey]
    _ ≤ ‖z * Work.Kernels.Kfun ℓ d w za‖
          + ‖(n : ℂ) * ((Work.Kernels.Kfun ℓ d ((1 : ℝ) +ᵥ w) za
              - Work.Kernels.Kfun ℓ d w za) * z - 1 / (2 * (Real.pi : ℂ)))‖ := norm_add_le _ _
    _ = ‖z‖ * ‖Work.Kernels.Kfun ℓ d w za‖
          + ‖(Work.Kernels.Kfun ℓ d ((1 : ℝ) +ᵥ w) za
              - Work.Kernels.Kfun ℓ d w za) * z - 1 / (2 * (Real.pi : ℂ))‖ := by
          rw [norm_mul, norm_mul, hn1, one_mul]
    _ ≤ ‖z‖ * (C₁ * (Work.Kernels.scale w) ^ N₁)
          + C₂ * (Work.Kernels.scale w) ^ N₂ * ‖z‖ := by
          refine add_le_add (mul_le_mul_of_nonneg_left hFval hC0) ?_
          have := hEval
          rwa [mul_comm] at this
    _ ≤ ‖z‖ * (C₁ * (Work.Kernels.scale w) ^ (max N₁ N₂))
          + C₂ * (Work.Kernels.scale w) ^ (max N₁ N₂) * ‖z‖ := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hNmax1 hC₁) hC0
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hNmax2 hC₂) hC0
    _ = (C₁ + C₂) * (Work.Kernels.scale w) ^ (max N₁ N₂) * ‖z‖ := by ring


/-- **The assigned theorem from the tile principal-part window.**  `Work.Asymptotics.TilePPWindow`
(`Submission/Work/Asymptotics/Tile/tileLayerDefs.lean`) is the un-guarded window form: for
`w ∈ E`, `n = ±1`, `t ∈ [Im w/2, 1]`,

  `‖K(n+ᵥw, i t) - (n/2π)/(i t - w)‖ ≤ C (scale w)^N`.

Multiplying by `‖i t - w‖` (legitimate exactly under the guard `i t ≠ w`, which every caller
supplies) gives the assigned Lipschitz form. -/
theorem tile_pp_uniform_lip_of_TilePPWindow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (h : Work.Asymptotics.TilePPWindow ℓ d) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) ≠
          Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            * (((t : ℂ) * Complex.I) - (w : ℂ)) - (n : ℂ) / (2 * (Real.pi : ℂ))‖
          ≤ C * (Work.Kernels.scale w) ^ N * ‖((t : ℂ) * Complex.I) - (w : ℂ)‖ := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, ?_⟩
  intro w hw n hn t ht h1 h2 hzw _
  have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) := by
    rw [Work.Kernels.Kaxis, dif_pos ht]
  have hb' := hb w hw n hn t h1 h2
  rw [hKax] at hb'
  set z : ℂ := (t : ℂ) * Complex.I - (w : ℂ) with hzdef
  have hsplit : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) * z
        - (n : ℂ) / (2 * (Real.pi : ℂ))
      = z * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)) := by
    have hz0 : z ≠ 0 := sub_ne_zero.mpr hzw
    rw [← hzdef]
    field_simp
  rw [hsplit, norm_mul]
  calc ‖z‖ * ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
      ≤ ‖z‖ * (C * (Work.Kernels.scale w) ^ N) :=
        mul_le_mul_of_nonneg_left hb' (norm_nonneg z)
    _ = C * (Work.Kernels.scale w) ^ N * ‖z‖ := by ring


/-- **The off-spike (`‖i t - w‖ ≥ Im w/8`) kernel bound in the cone-separated regime.**

From the new `Work.Asymptotics.TileWindow.tile_K_cone_sep` (the cone-separated bound for general
`ζ`, proved in `Submission/Work/Asymptotics/TileWindow/tile_K_cone_sep.lean`): on the contour
`ζ = i t` the cone condition `Im (S ζ) = 1/t ≥ 1` holds automatically because `t ≤ 1`, so only
the separation `dist (S ζ - S w, ℤ) ≥ 1/8` is needed.  The kernel is then `pp + (K - pp)` with
`‖pp‖ = (n/2π)/‖ζ - w‖ ≤ (4/π) (scale w)` in the off-spike regime. -/
theorem tile_K_far_cone_sep (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → w.im / 8 ≤ ‖((t : ℂ) * Complex.I - (w : ℂ))‖ →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖((ModularGroup.S • (Work.Kernels.imagAxis t ht) : UpperHalfPlane) : ℂ)
            - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.TileWindow.tile_K_cone_sep ℓ d hd
  have hspos : ∀ w : ℍ, 0 < Work.Kernels.scale w := fun w => Work.Kernels.scale_pos w
  refine ⟨C + 4 / Real.pi, max N 1, by positivity, le_trans hN (le_max_left N 1), ?_⟩
  intro w hw n hn t ht h1 h2 hfar hcone
  set ζ : ℍ := Work.Kernels.imagAxis t ht with hζdef
  have hζcoe : (ζ : ℂ) = (t : ℂ) * Complex.I := rfl
  -- the cone condition
  have hconez : 1 ≤ ((ModularGroup.S • ζ : UpperHalfPlane)).im := by
    rw [hζdef, Work.Asymptotics.im_S_smul_eq]
    have hζim : (ζ : ℂ).im = t := by rw [hζcoe]; simp
    have hζnorm : ‖(ζ : ℂ)‖ ^ 2 = t ^ 2 := by
      rw [hζcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, sq]
    rw [← UpperHalfPlane.coe_im ζ, hζim, hζnorm, le_div_iff₀ (by positivity)]
    nlinarith [ht, h2]
  have hsepζ : ∀ k : ℤ, (1 / 8 : ℝ) ≤
      ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
        - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ := by
    intro k; rw [hζdef]; exact hcone k
  have hmain : ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
        - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
      ≤ C * (Work.Kernels.scale w) ^ N := hb w hw n hn ζ hconez hsepζ
  have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ := by
    rw [hζdef, Work.Kernels.Kaxis, dif_pos ht]
  -- the geometric lower bound `‖ζ - w‖ ≥ (1/8)(scale w)^{-1}`
  have hlow : (Work.Kernels.scale w)⁻¹ ≤ w.im := by
    have hsw : (w.im)⁻¹ ≤ Work.Kernels.scale w := by
      simp only [Work.Kernels.scale]; linarith [norm_nonneg (w : ℂ)]
    rw [← inv_inv w.im, inv_le_inv₀ (hspos w) (by positivity)]
    exact hsw
  have hgap : (1 / 8 : ℝ) * (Work.Kernels.scale w)⁻¹ ≤ ‖(ζ : ℂ) - (w : ℂ)‖ := by
    rw [hζcoe]
    have ha : (1 / 8 : ℝ) * (Work.Kernels.scale w)⁻¹ ≤ (1 / 8 : ℝ) * w.im :=
      mul_le_mul_of_nonneg_left hlow (by norm_num)
    have hb' : (1 / 8 : ℝ) * w.im = w.im / 8 := by ring
    rw [hb'] at ha
    linarith [ha, hfar]
  -- the principal part
  have hpp : ‖((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
      ≤ (4 / Real.pi) * (Work.Kernels.scale w) ^ (max N 1) := by
    have hnm : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
    have hcc : ‖((n : ℂ) / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, hnm, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hpos : 0 < ‖(ζ : ℂ) - (w : ℂ)‖ :=
      lt_of_lt_of_le (mul_pos (by norm_num) (inv_pos.mpr (hspos w))) hgap
    have h8 : ‖(ζ : ℂ) - (w : ℂ)‖⁻¹ ≤ 8 * Work.Kernels.scale w := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      have hs : (0 : ℝ) < Work.Kernels.scale w := hspos w
      have h1' : (1 / 8 : ℝ) * (Work.Kernels.scale w)⁻¹ * (8 * Work.Kernels.scale w) = 1 := by
        calc (1 / 8 : ℝ) * (Work.Kernels.scale w)⁻¹ * (8 * Work.Kernels.scale w)
            = (1 / 8 : ℝ) * 8 * ((Work.Kernels.scale w)⁻¹ * Work.Kernels.scale w) := by ring
          _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt hs)]; norm_num
      have h2' := mul_le_mul_of_nonneg_right hgap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hs.le)
      rw [h1'] at h2'
      linarith [h2']
    have hsc : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have h3 : (Work.Kernels.scale w) ≤ (Work.Kernels.scale w) ^ (max N 1) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hsc (le_max_right N 1)
    rw [norm_mul, norm_inv, hcc]
    calc (1 / (2 * Real.pi)) * ‖(ζ : ℂ) - (w : ℂ)‖⁻¹
        ≤ (1 / (2 * Real.pi)) * (8 * Work.Kernels.scale w) :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = (4 / Real.pi) * Work.Kernels.scale w := by
          field_simp
          ring
      _ ≤ (4 / Real.pi) * (Work.Kernels.scale w) ^ (max N 1) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hX : ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
        - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
      ≤ C * (Work.Kernels.scale w) ^ (max N 1) := by
    have h2' : (Work.Kernels.scale w) ^ N ≤ (Work.Kernels.scale w) ^ (max N 1) :=
      Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_left N 1)
    exact le_trans hmain (mul_le_mul_of_nonneg_left h2' hC)
  have hsplit : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
      = (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹))
        + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹) := by ring
  rw [hKax, hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hfin : C * (Work.Kernels.scale w) ^ (max N 1)
        + (4 / Real.pi) * (Work.Kernels.scale w) ^ (max N 1)
      = (C + 4 / Real.pi) * (Work.Kernels.scale w) ^ (max N 1) := by ring
  linarith [hX, hpp, hfin.le, hfin.ge]

/-- **The off-spike window bound for the kernel remainder, from `tile_K_cone_sep`.**

At the contour point `ζ = i t` (`0 < t ≤ 1`) the cone condition `Im (S ζ) = 1/t ≥ 1` holds, so
the cone-separated bound `Work.Asymptotics.TileWindow.tile_K_cone_sep` applies as soon as
`dist (S ζ - S w, ℤ) ≥ 1/8`. -/
theorem offspike_window_own (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t), w.im / 2 ≤ t → t ≤ 1 →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖((ModularGroup.S • (Work.Kernels.imagAxis t ht) : UpperHalfPlane) : ℂ)
            - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.TileWindow.tile_K_cone_sep ℓ d hd
  refine ⟨C, N, hC, hN, ?_⟩
  intro w hw n hn t ht h1 h2 hsep
  set ζ : ℍ := Work.Kernels.imagAxis t ht with hζdef
  have hζcoe : (ζ : ℂ) = (t : ℂ) * Complex.I := rfl
  have hconez : 1 ≤ ((ModularGroup.S • ζ : UpperHalfPlane)).im := by
    rw [hζdef, Work.Asymptotics.im_S_smul_eq]
    have hζim : (ζ : ℂ).im = t := by rw [hζcoe]; simp
    have hζnorm : ‖(ζ : ℂ)‖ ^ 2 = t ^ 2 := by
      rw [hζcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, sq]
    rw [← UpperHalfPlane.coe_im ζ, hζim, hζnorm, le_div_iff₀ (by positivity)]
    nlinarith [ht, h2]
  have hsepζ : ∀ k : ℤ, (1 / 8 : ℝ) ≤
      ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
        - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ := by
    intro k; rw [hζdef]; exact hsep k
  have hmain := hb w hw n hn ζ hconez hsepζ
  rw [show Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ from by
    rw [hζdef, Work.Kernels.Kaxis, dif_pos ht]]
  exact hmain

/-- **The (guarded) tile principal-part window bound**, assembled from the off-spike bound
`offspike_window_own` (i.e. `tile_K_cone_sep`) and the maximum-modulus spike bound
`Work.Asymptotics.tilePPWindowSpike` (whose general-`ζ` input is again `tile_K_cone_sep`).

The split is the `S`-chart one: `∃ k, ‖S (i t) - S w - k‖ < 1/8` (the graze region, handled by
the maximum principle on the spike neighbourhood) versus `∀ k, 1/8 ≤ ‖S (i t) - S w - k‖`
(the cone-separated region, handled by `tile_K_cone_sep`). -/
theorem tile_pp_window_guarded (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t), w.im / 2 ≤ t → t ≤ 1 →
        ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C₁, N₁, hC₁, hN₁, h₁⟩ := offspike_window_own ℓ d hd
  obtain ⟨C₂, N₂, hC₂, hN₂, h₂⟩ :=
    Work.Asymptotics.tilePPWindowSpike ℓ d hd (Work.Asymptotics.TileWindow.tile_K_cone_sep ℓ d hd)
  refine ⟨max C₁ C₂, max N₁ N₂, le_max_of_le_left hC₁, le_max_of_le_left hN₁, ?_⟩
  intro w hw n hn t ht h1 h2 hne
  have hsc : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hsc
  have hCmax : (0 : ℝ) ≤ max C₁ C₂ := le_trans hC₁ (le_max_left _ _)
  have hm₁ : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hsc (le_max_left _ _)
  have hm₂ : (Work.Kernels.scale w) ^ N₂ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hsc (le_max_right _ _)
  by_cases hsp : ∃ k : ℤ, ‖((ModularGroup.S • (Work.Kernels.imagAxis t ht) : UpperHalfPlane) : ℂ)
      - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ < 1 / 8
  · refine le_trans (h₂ w hw n hn t ht h1 h2 hsp hne) ?_
    exact mul_le_mul (le_max_right _ _) hm₂ (Real.rpow_nonneg hsc0 _) hCmax
  · have hsep : ∀ k : ℤ, (1 / 8 : ℝ) ≤
        ‖((ModularGroup.S • (Work.Kernels.imagAxis t ht) : UpperHalfPlane) : ℂ)
          - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ :=
      fun k => not_lt.mp (fun hlt => hsp ⟨k, hlt⟩)
    refine le_trans (h₁ w hw n hn t ht h1 h2 hsep) ?_
    exact mul_le_mul (le_max_left _ _) hm₁ (Real.rpow_nonneg hsc0 _) hCmax

/-- **The uniform tile principal-part Lipschitz bound.** -/
theorem tile_pp_uniform_lip (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) ≠
          Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            * (((t : ℂ) * Complex.I) - (w : ℂ)) - (n : ℂ) / (2 * (Real.pi : ℂ))‖
          ≤ C * (Work.Kernels.scale w) ^ N * ‖((t : ℂ) * Complex.I - (w : ℂ))‖ := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_pp_window_guarded ℓ d hd
  refine ⟨C, N, hC, hN, ?_⟩
  intro w hw n hn t ht h1 h2 hzw _
  have hbw := hb w hw n hn t ht h1 h2 hzw
  rw [Work.Kernels.Kaxis, dif_pos ht] at hbw
  have hz0 : ((t : ℂ) * Complex.I - (w : ℂ)) ≠ 0 := sub_ne_zero.mpr hzw
  have hsplit : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
        * ((t : ℂ) * Complex.I - (w : ℂ)) - (n : ℂ) / (2 * (Real.pi : ℂ))
      = ((t : ℂ) * Complex.I - (w : ℂ))
        * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            - ((n : ℂ) / (2 * (Real.pi : ℂ)))
              * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)) := by
    field_simp
  rw [hsplit, norm_mul]
  calc ‖((t : ℂ) * Complex.I - (w : ℂ))‖
        * ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            - ((n : ℂ) / (2 * (Real.pi : ℂ)))
              * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
      ≤ ‖((t : ℂ) * Complex.I - (w : ℂ))‖ * (C * (Work.Kernels.scale w) ^ N) :=
        mul_le_mul_of_nonneg_left hbw (norm_nonneg _)
    _ = C * (Work.Kernels.scale w) ^ N * ‖((t : ℂ) * Complex.I) - (w : ℂ)‖ := by ring

end Work.Asymptotics.TileWindow
