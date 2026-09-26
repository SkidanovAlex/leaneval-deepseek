import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.Tile.tileWinDefs
import Submission.Work.Asymptotics.Tile.tile_dev_low
import Submission.Work.Asymptotics.Tile.halfDevFar8High
import Submission.Work.Asymptotics.Tile.halfDevFar24High
import Submission.Work.Asymptotics.Tile.halfDevFarMinus
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Asymptotics.Tile.tileFarTools

/-!
# The far regime `1 ≤ t ≤ Im (S • w) - 1` of the tile deviation

This file proves `Work.Asymptotics.Tile.tileWindowRestricted_far`: for `w ∈ E = KEpsilon` with
`w.re ≠ 0`, `n = ±1` and `1 ≤ t ≤ Im (S • w) - 1` the deviation
`Kaxis (Kfun ℓ d) (n +ᵥ w) t - Aexp (Gcusp ℓ d) (n +ᵥ w) t` is bounded by `C (scale w)^N t^M`.

## Route

* `1 ≤ t ≤ 3`: the low window `Work.Asymptotics.Tile.tile_dev_low` bounds the deviation
  `Kfun - Gfun` directly.
* `3 ≤ t ≤ Im (S • w) - 1`: the deviation splits as
  `Kfun - Gfun = ((K_+ - 𝒢_+) + (K_- - 𝒢_-)) / 2` (`Kernels.Kfun`, `Compact.gfun_eq`), and each
  half is polynomially bounded on the far window: `Work.Asymptotics.Tile.halfDevFar8High`,
  `...halfDevFarMinus` (and the `d = 24` plus half).
-/

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

/-! ## Absorption of exponents -/

/-- Two bounds of the shape `C s^N t^M` with `s, t ≥ 1` add up to one such bound. -/
private lemma pair_absorb {C1 N1 M1 C2 N2 M2 s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    C1 * s ^ N1 * t ^ M1 + C2 * s ^ N2 * t ^ M2
      ≤ (C1 + C2 + 1) * s ^ max N1 N2 * t ^ max M1 M2 := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h1N : s ^ N1 ≤ s ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
  have h2N : s ^ N2 ≤ s ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
  have h1M : t ^ M1 ≤ t ^ max M1 M2 :=
    Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _)
  have h2M : t ^ M2 ≤ t ^ max M1 M2 :=
    Real.rpow_le_rpow_of_exponent_le ht (le_max_right _ _)
  have hp1 : C1 * s ^ N1 * t ^ M1 ≤ C1 * s ^ max N1 N2 * t ^ max M1 M2 := by
    calc C1 * s ^ N1 * t ^ M1 = C1 * (s ^ N1 * t ^ M1) := by ring
      _ ≤ C1 * (s ^ max N1 N2 * t ^ max M1 M2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1N h1M (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hs0.le _)) hC1
      _ = C1 * s ^ max N1 N2 * t ^ max M1 M2 := by ring
  have hp2 : C2 * s ^ N2 * t ^ M2 ≤ C2 * s ^ max N1 N2 * t ^ max M1 M2 := by
    calc C2 * s ^ N2 * t ^ M2 = C2 * (s ^ N2 * t ^ M2) := by ring
      _ ≤ C2 * (s ^ max N1 N2 * t ^ max M1 M2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h2N h2M (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hs0.le _)) hC2
      _ = C2 * s ^ max N1 N2 * t ^ max M1 M2 := by ring
  have hbase : (0 : ℝ) ≤ s ^ max N1 N2 * t ^ max M1 M2 :=
    mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg ht0.le _)
  calc C1 * s ^ N1 * t ^ M1 + C2 * s ^ N2 * t ^ M2
      ≤ C1 * s ^ max N1 N2 * t ^ max M1 M2 + C2 * s ^ max N1 N2 * t ^ max M1 M2 :=
        add_le_add hp1 hp2
    _ = (C1 + C2) * (s ^ max N1 N2 * t ^ max M1 M2) := by ring
    _ ≤ (C1 + C2 + 1) * (s ^ max N1 N2 * t ^ max M1 M2) := by
        refine mul_le_mul_of_nonneg_right ?_ hbase
        linarith
    _ = (C1 + C2 + 1) * s ^ max N1 N2 * t ^ max M1 M2 := by ring

/-- A bound `C s^N t^M` is monotone in the exponents and the constant, for `s, t ≥ 1`. -/
private lemma absorb_mono {C N M C' N' M' s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hCC : C ≤ C') (hN : N ≤ N') (hM : M ≤ M') :
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
    _ ≤ C' * (s ^ N' * t ^ M') := mul_le_mul hCC h3 h3nn (le_trans hC hCC)
    _ = C' * s ^ N' * t ^ M' := by ring

/-- A linear bound (no `t^M` factor) upgrades to the target shape using `t ≥ 1`. -/
private lemma absorb_lin {C N C' N' M' s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hCC : C ≤ C') (hN : N ≤ N') (hM0 : 0 ≤ M') :
    C * s ^ N ≤ C' * s ^ N' * t ^ M' := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have h1 : s ^ N ≤ s ^ N' := Real.rpow_le_rpow_of_exponent_le hs hN
  have h2 : (1 : ℝ) ≤ t ^ M' := Real.one_le_rpow ht hM0
  calc C * s ^ N ≤ C' * s ^ N := mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hs0.le N)
    _ = C' * s ^ N * 1 := by ring
    _ ≤ C' * s ^ N * t ^ M' := by
        refine mul_le_mul_of_nonneg_left h2 ?_
        exact mul_nonneg (le_trans hC hCC) (Real.rpow_nonneg hs0.le N)
    _ ≤ C' * s ^ N' * t ^ M' := by
        have hbase : (0 : ℝ) ≤ t ^ M' := Real.rpow_nonneg (le_trans zero_le_one ht) M'
        calc C' * s ^ N * t ^ M' = C' * (s ^ N * t ^ M') := by ring
          _ ≤ C' * (s ^ N' * t ^ M') :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right h1 hbase) (le_trans hC hCC)
          _ = C' * s ^ N' * t ^ M' := by ring

/-! ## The two half-deviations on the far window -/

/-- The `K_+` half of the far window (both dimensions). -/
private theorem kplus_far (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → 3 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  rcases hd with rfl | rfl
  · exact halfDevFar8High
  · exact halfDevFar24High

/-! ## The assembly -/

theorem tileWindowRestricted_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → w.re ≠ 0 → ∀ (n : ℤ),
        (n = 1 ∨ n = -1) → ∀ t : ℝ, 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨Cp, Np, Mp, hCp, hNp, hMp, hbp⟩ := kplus_far d hd
  obtain ⟨Cm, Nm, Mm, hCm, hNm, hMm, hbm⟩ := halfDevFarMinus ℓ d hd
  obtain ⟨Cl, Nl, hCl, hNl, hbl⟩ := tile_dev_low ℓ d hd
  set Nh : ℝ := max (max Np Nm) Nl with hNh
  set Mh : ℝ := max (max Mp Mm) 0 with hMh
  refine ⟨(Cp + Cm + 1) + Cl + 1, Nh, Mh, by positivity, ?_, ?_, ?_⟩
  · exact le_max_of_le_left (le_max_of_le_left hNp)
  · exact le_max_of_le_right (le_refl (0 : ℝ))
  · intro w hw hre n hn t ht1 htle
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
    have hNh1 : max (max Np Nm) Nl ≤ Nh := le_of_eq hNh.symm
    have hMh1 : max (max Mp Mm) 0 ≤ Mh := le_of_eq hMh.symm
    have hNp' : Np ≤ Nh := le_trans (le_max_of_le_left (le_max_of_le_left (le_refl Np))) hNh1
    have hNm' : Nm ≤ Nh := le_trans (le_max_of_le_left (le_max_of_le_right (le_refl Nm))) hNh1
    have hNl' : Nl ≤ Nh := le_trans (le_max_of_le_right (le_refl Nl)) hNh1
    have hMp' : Mp ≤ Mh := le_trans (le_max_of_le_left (le_max_of_le_left (le_refl Mp))) hMh1
    have hMm' : Mm ≤ Mh := le_trans (le_max_of_le_left (le_max_of_le_right (le_refl Mm))) hMh1
    have hM0' : (0 : ℝ) ≤ Mh := le_trans (le_max_of_le_right (le_refl (0 : ℝ))) hMh1
    have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) := by
      rw [Work.Kernels.Kaxis, dif_pos ht0]
    have hAexp : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t
        = Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) :=
      Aexp_Gcusp_eq_Gfun' ℓ d hd ((n : ℝ) +ᵥ w) t ht0
    by_cases hcase : t ≤ 3
    · rw [hKax, hAexp]
      have hl := hbl w hw n hn t ht0 ht1 hcase
      refine le_trans hl ?_
      exact absorb_lin hs1 ht1 hCl.le (by linarith [hCp, hCm, hCl]) hNl' hM0'
    · push_neg at hcase
      have h3 : (3 : ℝ) ≤ t := le_of_lt hcase
      rw [hKax, hAexp]
      have hsplit : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
          = ((Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0))
              + (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                    (Work.Kernels.imagAxis t ht0))) / 2 := by
        have hg := Work.Asymptotics.Compact.gfun_eq ℓ d hd ((n : ℝ) +ᵥ w)
          (Work.Kernels.imagAxis t ht0)
        have hg2 : Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w)
              (Work.Kernels.imagAxis t ht0)
            = (Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                + Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                    (Work.Kernels.imagAxis t ht0)) / 2 := by
          rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), hg]
          ring
        simp only [Work.Kernels.Kfun, hg2]
        ring
      rw [hsplit, norm_div]
      have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2c]
      have hb1 := hbp w n (Work.Kernels.imagAxis t ht0) t hn hw rfl h3 htle
      have hb2 := hbm w n (Work.Kernels.imagAxis t ht0) t hn hw rfl h3 htle
      set X : ℝ := ((Cp + Cm + 1) + Cl + 1) * (Work.Kernels.scale w) ^ Nh * t ^ Mh with hXdef
      have hX0 : 0 ≤ X := by
        rw [hXdef]
        exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hs0.le _))
          (Real.rpow_nonneg (le_trans zero_le_one ht1) _)
      have htri : ‖(Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0))
              + (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                    (Work.Kernels.imagAxis t ht0))‖
          ≤ (Cp * (Work.Kernels.scale w) ^ Np * t ^ Mp)
            + (Cm * (Work.Kernels.scale w) ^ Nm * t ^ Mm) :=
        le_trans (norm_add_le _ _) (add_le_add hb1 hb2)
      have hup : (Cp * (Work.Kernels.scale w) ^ Np * t ^ Mp)
            + (Cm * (Work.Kernels.scale w) ^ Nm * t ^ Mm) ≤ X := by
        rw [hXdef]
        refine le_trans (pair_absorb hs1 ht1 hCp.le hCm.le) ?_
        refine absorb_mono (C := Cp + Cm + 1) (N := max Np Nm) (M := max Mp Mm)
          (C' := (Cp + Cm + 1) + Cl + 1) (N' := Nh) (M' := Mh) hs1 ht1
          (by positivity) (by linarith [hCl]) ?_ ?_
        · exact le_trans (le_max_of_le_left (le_refl (max Np Nm))) hNh1
        · exact le_trans (le_max_of_le_left (le_refl (max Mp Mm))) hMh1
      have hle : ‖(Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0))
              + (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                    (Work.Kernels.imagAxis t ht0))‖ ≤ X := le_trans htri hup
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith

end Work.Asymptotics.Tile
