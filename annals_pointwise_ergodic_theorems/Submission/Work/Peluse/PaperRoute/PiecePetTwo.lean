import Mathlib
import Submission.Work.Peluse.UControl.assemblyDefs

/-!
# `PiecePetTwo`: the level-`≥ 2` form of the chapter `PiecePet`

`Work.Peluse.UControl.PiecePet P` (`assemblyDefs.lean`, frozen statement layer) records its level as

  `∃ s₀ : ℕ, 1 ≤ s₀ ∧ …`,

which is **not enough for any consumer that needs a level `s ≥ 2`**: the crux `PeluseCrux` uses one
common level `s` for the `U^s`-control (`PeluseUControl`/`PeluseUControlPaper`) *and* for the
degree-lowering chapter `PeluseULowering`, whose quantification is `∀ s, 2 ≤ s → …`
(`Nodes.lean`).  Since the Gowers norms *decrease* in the level, a level-`1` bound is strictly
weaker and there is no transfer `uNormPow 1 ≤ c·uNormPow s` for `s ≥ 2` in the tree (the only
transfer, `uNormPow_level_raise_win 1 2`, runs the other way: `c·(U¹)^2 ≤ U²`).

Equivalently: `PiecePet`'s obligation *must* be stated at a level `s₀ ≥ 2` (the record
`Submission/Work/Peluse/UControl/piecePet.lean`, §"What a proof needs", notes that at level `1` the
matched-character family of `LevelOneInput` has `‖ΛZ‖ ≈ 0.99` while `uNormPow 1 = O(L⁻²) → 0`).

`PiecePetTwo P` is `PiecePet`'s body with `1 ≤ s₀` replaced by `2 ≤ s₀`.  It is *strictly stronger*
than `PiecePet` (`PiecePet_of_PiecePetTwo` below), every producer of `PiecePet` in the tree that
goes through a level-`s ≥ 2` chapter produces it verbatim (`Prop36SW`, `BandAprime`, …), and it is
the form the paper-route wiring `PaperRoute/ucontrolPaper_of_piecePet.lean` consumes.

See `NOTES_PaperRoute_Q1_BLOCKER_prop36S_FALSE.md` and `NOTES_ucontrol_of_concat_SESSION23.md`.

## Recipe for the consumer `PaperRoute/ucontrolPaper_of_piecePet.lean` (Q2)

The consumer is the same statement as the **proved**
`Work.Peluse.ucontrol_of_concat_of_chapterWith` (`Submission/Work/Peluse/ucontrol_of_concat.lean`)
with the all-`D` chapter `Work.Peluse.UControl.Theorem37ChapterWith` replaced by `PiecePetTwo`; its
proof body is the recipe.  Proved bridges it uses, all re-usable: `Pairing.cs_dualFn_step`,
`Pairing.dualFn_supportIn_dSup`, `LambdaZ_scale`, `norm_dualFn_le_one` and `boxNormPow_symIcc_ratio`
and `uNormPow_star` (all in the node file `ucontrol_of_concat.lean`),
`Work.Peluse.UControl.uNormPow_direction_bridge`, `UControl.arith_chapter_hyp`, `UControl.arith_final`,
`polySup_le_sum_coeff_mul_pow`, `lc_natAbs_mul_pow_le_polySup`.

Steps: (1) unwrap `s₀ ≥ 2`, and for `A' ≥ 1` set `A'' := A' + CP`
(`CP := ∑ i ∈ Finset.range (d+1), (P.coeff i).natAbs`), get `Cp`, `Kp` from the chapter, take
`K := 4 * Kp` and the same `C : ℕ := max 1 (Nat.ceil (max (Cp * A'' ^ (5*Kp) * 3 ^ (2*Kp) / kap) 1))`
as the template, with `kap > 0` the constant of
`UControl.uNormPow_direction_bridge hs₀ P.natDegree.factorial (by omega)`.
(2) `MA := dSup P N₀ N`, `F := dualFn N P f₀ f₁`, `δ₂ := δ^2 * N₀^2 / ((2*MA+1)*MA)`; Corollary 3.8
(`Pairing.cs_dualFn_step` + `LambdaZ_scale`) gives `δ₂ ≤ ‖LambdaZ MA N P f₀ f₁ (star ∘ F)‖`.
(3) `D := ⌊δ^K * (N:ℝ)^d / (C:ℝ)⌋₊`, `δ' := (D:ℝ)/(N:ℝ)^d`, so `dirLen P δ' N = D` (a
`floor_div_pow_mul_pow`-style computation).  (4) Apply the chapter to the `Hyp`-datum
`(A' := A'', C := A''*Cp, K := K)` on `(N, N₁ := MA, g₀ := f₀, g₁ := f₁, g₂ := star ∘ F, γ := δ₂,
δ' := δ')`: the gauge holds by construction; the fit `dirCoeff P * D ≤ MA` follows from `N^d ≤ MA`
(the template's `hMAnat`) and `dirCoeff P * D ≤ N^d` for `δ ≤ 1`.  **Choose `K₂` large** so that
`(C:ℝ) * δ^{-K₂} ≤ N` forces the `Hyp` window conjunct `1 ≤ ⌊δ' * N⌋` and `1 ≤ D` — the one place
the target's non-degeneracy is used (the template did not need it).  (5) Use
`UControl.uNormPow_direction_bridge` at `M := P.natDegree.factorial` and then `uNormPow_star` to
reach the goal's direction set and function, and finish with `UControl.arith_final`.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- **The level-`≥ 2` form of `PiecePet`**: the same data, the same gauge `A'·Cp ≤ C` and the same
direction fit `κ·L ≤ N₁`, with the level recorded as `2 ≤ s₀`. -/
def PiecePetTwo (P : Polynomial ℤ) : Prop :=
  ∃ s₀ : ℕ, 2 ≤ s₀ ∧ ∀ A' : ℝ, 1 ≤ A' →
    ∃ Cp : ℝ, 1 ≤ Cp ∧ ∃ Kp : ℕ, 1 ≤ Kp ∧
    ∀ (C : ℝ), 1 ≤ C → ∀ (K : ℕ), Kp ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      A' * Cp ≤ C →
      (dirCoeff P) * (dirLen P δ' N : ℤ) ≤ (N₁ : ℤ) →
      Concl P A' Cp K N N₁ g₂ γ δ' s₀

/-- `PiecePetTwo` implies `PiecePet` (the level hypothesis is the only difference, and it is
weakened).  So every consumer of `PiecePet` keeps working. -/
theorem PiecePet_of_PiecePetTwo {P : Polynomial ℤ} (h : PiecePetTwo P) : PiecePet P := by
  obtain ⟨s₀, hs₀, hrest⟩ := h
  exact ⟨s₀, le_trans (by norm_num : 1 ≤ (2 : ℕ)) hs₀, hrest⟩

end

end Work.Peluse.UControl
