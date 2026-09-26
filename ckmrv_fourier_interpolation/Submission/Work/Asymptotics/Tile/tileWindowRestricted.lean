import Mathlib
import Submission.Work.Asymptotics.Tile.tileWinDefs
import Submission.Work.Asymptotics.Tile.tileBelowPoleTop
import Submission.Work.Asymptotics.Tile.tile_dev_low
import Submission.Work.Asymptotics.Tile.tileWindowRestricted_far
import Submission.Work.Asymptotics.Tile.tileWindowRestricted_strip

/-!
# The below-pole window on the cusp-`±1` tiles, restricted to `Re w ≠ 0`

The target `Work.Asymptotics.Tile.tileWindowRestricted` bounds the deviation

  `Kaxis (Kfun ℓ d) (n +ᵥ w) t - Aexp (Gcusp ℓ d) (n +ᵥ w) t`

for `w ∈ E = KEpsilon` with `Re w ≠ 0`, `n = ±1` and `1 ≤ t ≤ 2 Im (S • w) + 1`
by a polynomial `C (scale w)^N t^M`.

## The reduction

The `t`-range is split at `t = 3` and at the two pole-height boundaries
`Im (S • w) ± 1`:

* `1 ≤ t ≤ 3` is the low window `Work.Asymptotics.Tile.tile_dev_low` (proved);
* `1 ≤ t ≤ Im (S • w) - 1` is the far regime, supplied by
  `Work.Asymptotics.Tile.tileWindowRestricted_far`;
* `Im (S • w) - 1 ≤ t ≤ Im (S • w) + 1` is the resonant strip, supplied by
  `Work.Asymptotics.Tile.tileWindowRestricted_strip`;
* `Im (S • w) + 1 ≤ t ≤ 2 Im (S • w) + 1` is the below-pole top window
  `Work.Asymptotics.Tile.tileBelowPoleTop` (proved).

The two missing regimes are the delegated lemmas; everything else (including the
bookkeeping of the constants) is proved here.
-/

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

/-- Rewrite the target's left-hand side, using `z = i t`, as the difference `Kfun - Gfun`. -/
private lemma axisAexp_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
      = Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)
        - Work.Asymptotics.Compact.Gfun d ℓ τ (Work.Kernels.imagAxis t ht) := by
  rw [Work.Kernels.Kaxis, dif_pos ht, Work.Asymptotics.Gcusp_eq_Gcoef ℓ d hd,
    Work.Asymptotics.Aexp_Gcoef' ℓ d τ t ht]

/-- Monotonicity of `s^N t^M` in the two exponents. -/
private lemma absorb_bound {s t C C' N N' M M' : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hC' : C ≤ C') (hN : N ≤ N') (hM : M ≤ M') :
    C * s ^ N * t ^ M ≤ C' * s ^ N' * t ^ M' := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : s ^ N ≤ s ^ N' := Real.rpow_le_rpow_of_exponent_le hs hN
  have h2 : t ^ M ≤ t ^ M' := Real.rpow_le_rpow_of_exponent_le ht hM
  have h3 : s ^ N * t ^ M ≤ s ^ N' * t ^ M' :=
    mul_le_mul h1 h2 (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hs0.le _)
  have h3nn : (0 : ℝ) ≤ s ^ N * t ^ M :=
    mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg ht0.le _)
  calc C * s ^ N * t ^ M = C * (s ^ N * t ^ M) := by ring
    _ ≤ C' * (s ^ N' * t ^ M') := mul_le_mul hC' h3 h3nn (le_trans hC hC')
    _ = C' * s ^ N' * t ^ M' := by ring

/-- **The assembly.**  The target follows from the far and strip bounds for the tile. -/
theorem tileWindowRestricted_of_pieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hfar : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → w.re ≠ 0 → ∀ (n : ℤ),
        (n = 1 ∨ n = -1) → ∀ t : ℝ, 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M)
    (hstrip : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → w.re ≠ 0 → ∀ (n : ℤ),
        (n = 1 ∨ n = -1) → ∀ t : ℝ, (ModularGroup.S • w).im - 1 ≤ t →
          t ≤ (ModularGroup.S • w).im + 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        w.re ≠ 0 → ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨Cf, Nf, Mf, hCf, hNf, hMf, hfarb⟩ := hfar
  obtain ⟨Cs, Ns, Ms, hCs, hNs, hMs, hstripb⟩ := hstrip
  obtain ⟨Ct, Nt, Mt, hCt, hNt, hMt, htopb⟩ := tileBelowPoleTop ℓ d hd
  obtain ⟨Cl, Nl, hCl, hNl, hlowb⟩ := tile_dev_low ℓ d hd
  refine ⟨max (max Cl Cf) (max Cs Ct) + 1, max (max Nl Nf) (max Ns Nt),
    max (max Mf Ms) Mt, by positivity, ?_, ?_, ?_⟩
  · exact le_trans hNl (le_trans (le_max_left Nl Nf) (le_max_left _ _))
  · exact le_trans hMf (le_trans (le_max_left Mf Ms) (le_max_left _ _))
  · intro w n hn hw hre t ht1 ht2
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hs1 : 1 ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
    have hNl' : Nl ≤ max (max Nl Nf) (max Ns Nt) :=
      le_trans (le_max_left Nl Nf) (le_max_left _ _)
    have hNf' : Nf ≤ max (max Nl Nf) (max Ns Nt) :=
      le_trans (le_max_right Nl Nf) (le_max_left _ _)
    have hNs' : Ns ≤ max (max Nl Nf) (max Ns Nt) :=
      le_trans (le_max_left Ns Nt) (le_max_right _ _)
    have hNt' : Nt ≤ max (max Nl Nf) (max Ns Nt) :=
      le_trans (le_max_right Ns Nt) (le_max_right _ _)
    have hMf' : Mf ≤ max (max Mf Ms) Mt := le_trans (le_max_left Mf Ms) (le_max_left _ _)
    have hMs' : Ms ≤ max (max Mf Ms) Mt := le_trans (le_max_right Mf Ms) (le_max_left _ _)
    have hMt' : Mt ≤ max (max Mf Ms) Mt := le_max_right _ _
    have hM0 : (0 : ℝ) ≤ max (max Mf Ms) Mt :=
      le_trans hMf (le_trans (le_max_left Mf Ms) (le_max_left _ _))
    have hCl' : Cl ≤ max (max Cl Cf) (max Cs Ct) + 1 := by
      have h : Cl ≤ max (max Cl Cf) (max Cs Ct) := le_trans (le_max_left Cl Cf) (le_max_left _ _)
      linarith
    have hCf' : Cf ≤ max (max Cl Cf) (max Cs Ct) + 1 := by
      have h : Cf ≤ max (max Cl Cf) (max Cs Ct) := le_trans (le_max_right Cl Cf) (le_max_left _ _)
      linarith
    have hCs' : Cs ≤ max (max Cl Cf) (max Cs Ct) + 1 := by
      have h : Cs ≤ max (max Cl Cf) (max Cs Ct) := le_trans (le_max_left Cs Ct) (le_max_right _ _)
      linarith
    have hCt' : Ct ≤ max (max Cl Cf) (max Cs Ct) + 1 := by
      have h : Ct ≤ max (max Cl Cf) (max Cs Ct) := le_trans (le_max_right Cs Ct) (le_max_right _ _)
      linarith
    by_cases h3 : t ≤ 3
    · have hl := hlowb w hw n hn t ht ht1 h3
      have htM : (1 : ℝ) ≤ t ^ (max (max Mf Ms) Mt) := Real.one_le_rpow ht1 hM0
      have hstep : Cl * (Work.Kernels.scale w) ^ Nl
          ≤ Cl * (Work.Kernels.scale w) ^ Nl * t ^ (max (max Mf Ms) Mt) := by
        calc Cl * (Work.Kernels.scale w) ^ Nl
            = Cl * (Work.Kernels.scale w) ^ Nl * 1 := (mul_one _).symm
          _ ≤ Cl * (Work.Kernels.scale w) ^ Nl * t ^ (max (max Mf Ms) Mt) :=
              mul_le_mul_of_nonneg_left htM (mul_nonneg hCl.le (Real.rpow_nonneg hsc0 _))
      refine le_trans (le_trans (by
        simpa [axisAexp_eq ℓ d hd ((n : ℝ) +ᵥ w) t ht] using hl) hstep) ?_
      exact absorb_bound hs1 ht1 hCl.le hCl' hNl' (le_refl _)
    · push_neg at h3
      by_cases h4 : t ≤ (ModularGroup.S • w).im - 1
      · refine le_trans (by
          simpa [axisAexp_eq ℓ d hd ((n : ℝ) +ᵥ w) t ht] using
            hfarb w hw hre n hn t ht1 h4) ?_
        exact absorb_bound hs1 ht1 hCf.le hCf' hNf' hMf'
      · push_neg at h4
        by_cases h5 : t ≤ (ModularGroup.S • w).im + 1
        · refine le_trans (by
            simpa [axisAexp_eq ℓ d hd ((n : ℝ) +ᵥ w) t ht] using
              hstripb w hw hre n hn t (le_of_lt h4) h5) ?_
          exact absorb_bound hs1 ht1 hCs.le hCs' hNs' hMs'
        · push_neg at h5
          refine le_trans (by
            simpa [axisAexp_eq ℓ d hd ((n : ℝ) +ᵥ w) t ht] using
              htopb w hw n hn t (le_of_lt h5) ht2) ?_
          exact absorb_bound hs1 ht1 hCt.le hCt' hNt' hMt'

end Work.Asymptotics.Tile

namespace Work.Asymptotics.Tile

/-- **The below-pole window on the cusp-`±1` tiles, restricted to `Re w ≠ 0`.** -/
theorem tileWindowRestricted (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        w.re ≠ 0 → ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M :=
  tileWindowRestricted_of_pieces ℓ d hd
    (tileWindowRestricted_far ℓ d hd) (tileWindowRestricted_strip ℓ d hd)

end Work.Asymptotics.Tile
