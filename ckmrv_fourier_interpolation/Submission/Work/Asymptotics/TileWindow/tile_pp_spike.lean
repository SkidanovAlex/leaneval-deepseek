/-
# The tile principal-part spike bound

The assigned target `Work.Asymptotics.TileWindow.tile_pp_spike` is the *spike* (near-pole)
form of the Lipschitz bound for the tile kernel remainder

    `R(ζ) = K^{(d)}(n +ᵥ w, ζ) - (n/2π)(ζ - w)⁻¹`,

restricted to the imaginary axis and to the neighbourhood `‖i t - w‖ ≤ Im w / 8` of the
translate pole `ζ = w` (`n = ± 1`, `w ∈ E = KEpsilon`).

The route taken here is the one the workspace has already assembled for the *full* window:
`R` splits according to whether the `S`-image `i/t` of the contour point is within `1/8` of a
lattice translate of `S • w` or not,

* **off spike** (`∀ k, 1/8 ≤ ‖i/t - S • w - k‖`): `Work.Asymptotics.offspike_window_bound`
  (from `tile_divisor_lower_cone`, `tileXi_poly` and the `Ncusp` cone bound `tile_ncusp_own`),
* **on spike** (`∃ k, ‖i/t - S • w - k‖ < 1/8`): `Work.Asymptotics.tilePPWindowSpike`, the
  maximum-modulus argument that turns the off-spike bound into the on-spike bound.

Both inputs are sorry-free, and their conjunction gives the unguarded window bound
`Work.Asymptotics.TileWindow.tile_pp_window_full` for *every* `t ∈ [Im w / 2, 1]` and `n = ± 1`
(with `i t ≠ w`).  Multiplying by `‖i t - w‖` (which is legitimate exactly because `i t ≠ w`)
yields the assigned statement: its extra hypotheses `‖i t - w‖ ≤ Im w / 8` and
`j (i t) ≠ j (n +ᵥ w)` are simply not needed.

## Main results

* `Work.Asymptotics.TileWindow.tile_pp_window_full` — the unguarded window bound.
* `Work.Asymptotics.TileWindow.tile_pp_spike` — the assigned lemma.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.TileWindow.tile_K_cone_sep
import Submission.Work.Asymptotics.TileWindow.tile_pp_uniform_lip
import Submission.Work.Asymptotics.TileWindow.tile_ncusp_own
import Submission.Work.Asymptotics.offspike_bound_general
import Submission.Work.Asymptotics.tilePPWindowSpike

namespace Work.Asymptotics.TileWindow

open UpperHalfPlane ModularGroup

/-- The `S`-image of a contour point `i t` (`t > 0`) is `i / t`. -/
lemma coe_S_imagAxis (t : ℝ) (ht : 0 < t) :
    ((ModularGroup.S • Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
      = Complex.I / (t : ℂ) := by
  rw [div_eq_mul_inv]
  have hcoe : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg, hcoe]
  field_simp
  rw [Complex.I_sq]
  ring

/-- **The unguarded tile principal-part window bound.**  For `w ∈ E = KEpsilon`, `n = ± 1` and
every `t ∈ [Im w / 2, 1]` with `i t ≠ w`, the kernel at the tile point `n +ᵥ w` differs from
the principal part `(n/2π)(i t - w)⁻¹` of its translate pole by at most `C (scale w)^N`.

This is the conjunction of the off-spike bound `offspike_window_bound` and the spike bound
`tilePPWindowSpike`; both apply on the complement of each other's hypothesis. -/
theorem tile_pp_window_full (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨c, C₀, N₀, hc₀, hclt, hC₀, hN₀, hNc⟩ := tile_ncusp_own ℓ d hd
  have hNc' : ∃ c C N : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ c ∧ c < 2 * Real.pi ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (c * ((ModularGroup.S • w).im - z.im))) :=
    ⟨c, C₀, N₀, hC₀, hN₀, hc₀, hclt, hNc⟩
  obtain ⟨C₁, N₁, hC₁, hN₁, hw₁⟩ := offspike_window_bound ℓ d hd hNc'
  obtain ⟨C₂, N₂, hC₂, hN₂, hw₂⟩ :=
    tilePPWindowSpike ℓ d hd (Work.Asymptotics.offspike_bound_E ℓ d hd hNc')
  refine ⟨max C₁ C₂, max N₁ N₂, le_max_of_le_left hC₁, le_max_of_le_left hN₁, ?_⟩
  intro w hw n hn t ht h1 h2 hne
  have hsc : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hsc
  have hC₁' : (0 : ℝ) ≤ max C₁ C₂ := le_trans hC₁ (le_max_left _ _)
  have hm₁ : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hsc (le_max_left _ _)
  have hm₂ : (Work.Kernels.scale w) ^ N₂ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hsc (le_max_right _ _)
  have hSco := coe_S_imagAxis t ht
  by_cases hsp : ∃ k : ℤ,
      ‖((ModularGroup.S • Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
        - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ < 1 / 8
  · refine le_trans (hw₂ w hw n hn t ht h1 h2 hsp hne) ?_
    exact mul_le_mul (le_max_right _ _) hm₂ (Real.rpow_nonneg hsc0 _) hC₁'
  · have hsep : ∀ k : ℤ, (1 / 8 : ℝ) ≤
        ‖Complex.I / (t : ℂ)
          - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ := by
      intro k
      have hk : ¬ (‖((ModularGroup.S • Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
          - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ < 1 / 8) :=
        fun hlt => hsp ⟨k, hlt⟩
      rw [hSco] at hk
      exact not_lt.mp hk
    refine le_trans (hw₁ w hw n hn t h1 h2 hsep) ?_
    exact mul_le_mul (le_max_left _ _) hm₁ (Real.rpow_nonneg hsc0 _) hC₁'

theorem tile_pp_spike (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
        w.im / 2 ≤ t → t ≤ 1 → ‖((t : ℂ) * Complex.I - (w : ℂ))‖ ≤ w.im / 8 →
        ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) ≠
          Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            * (((t : ℂ) * Complex.I) - (w : ℂ)) - (n : ℂ) / (2 * (Real.pi : ℂ))‖
          ≤ C * (Work.Kernels.scale w) ^ N * ‖((t : ℂ) * Complex.I) - (w : ℂ)‖ := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_pp_window_full ℓ d hd
  refine ⟨C, N, hC, hN, ?_⟩
  intro w hw n hn t ht h1 h2 _ hne _
  have hbw := hb w hw n hn t ht h1 h2 hne
  rw [Work.Kernels.Kaxis, dif_pos ht] at hbw
  set z : ℂ := (t : ℂ) * Complex.I - (w : ℂ) with hz
  have hz0 : z ≠ 0 := sub_ne_zero.mpr hne
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
