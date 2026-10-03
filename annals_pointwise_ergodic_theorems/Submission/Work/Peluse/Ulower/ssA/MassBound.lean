/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.ssA.GapLocalAna
import Submission.Work.Peluse.Ulower.iterDelta_tsum_le
import Submission.Work.Peluse.Ulower.iterDelta_finsupp_bound
import Submission.Work.Peluse.Ulower.dualFn_tsum_le

/-!
# The `ℓ¹`-mass bound from the "many shifts" hypothesis

`Work.Peluse.Ulower.ss_mass_bound_of_manyShifts`: if `ManyShiftsHypδ P s N₀ N D f₀ f₁ δ` holds in
the gap regime, then the `ℓ¹`-mass of `f₁` is at least `(δ/4)·|symIcc (dSup P N₀ N)|`:

`δ / 4 * (2 * dSup P N₀ N + 1) ≤ ∑'_x ‖f₁ x‖`.

This is the "mass" or "no-cancellation" input of the gap case: it is what makes the elementary
branch (`q` larger than the support window, so the progression average has no cancellation) work.
It is the same statement as `Work.Peluse.Ulower.mass_bound_of_manyShifts`
(`Ulower/gap_extraction.lean`), restated here so that it can be *imported*: the original lives in a
file whose closure contains the two name clashes recorded in
`NOTES_ULower_BLOCKERS_2026-09-29.md` §1–§2, while this module imports only clash-free modules.

Proof: the many-shifts hypothesis gives a shift tuple `sh` with
`δ/4 ≤ ‖F‖_{□²_{c[D]}(symIcc (dSup P N₀ N))}` for `F = iterDelta (s-2) sh (dualFn N P f₀ f₁)`; the
box norm is bounded by the `ℓ¹`-mass of `F` over the box
(`boxNormPow_le_mass`), the iterated difference does not increase the `ℓ¹`-mass
(`iterDelta_tsum_le`), and the `ℓ¹`-mass of the dual function is at most that of `f₁`
(`dualFn_tsum_le`).
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower.SsA

noncomputable section

open Work.Peluse

/-- A finitely supported function is `ℓ¹`-summable. -/
private lemma summable_norm_of_finSuppZ {F : ℤ → ℂ} (h : Work.Peluse.FinSuppZ F) :
    Summable (fun x : ℤ => ‖F x‖) := by
  obtain ⟨N, hN⟩ := h
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun x hx => ?_)
  have hx' : N < x.natAbs := by
    rw [Finset.mem_Icc] at hx
    rw [not_and_or] at hx
    rcases hx with hx | hx
    · have h1 : x < -(N : ℤ) := not_le.mp hx
      have h2 : (0 : ℤ) ≤ -x := by omega
      have h3 : (x.natAbs : ℤ) = -x := by
        have h4 := Int.natAbs_of_nonneg h2
        rwa [Int.natAbs_neg] at h4
      have : (N : ℤ) < (x.natAbs : ℤ) := by rw [h3]; omega
      exact_mod_cast this
    · have h1 : (N : ℤ) < x := not_le.mp hx
      have h2 : (0 : ℤ) ≤ x := by omega
      have h3 : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg h2
      have : (N : ℤ) < (x.natAbs : ℤ) := by rw [h3]; omega
      exact_mod_cast this
  rw [hN x hx', norm_zero]

/-- **The `ℓ¹`-mass bound of the gap regime.**  If the "many shifts" hypothesis holds (at level
`δ`) in the gap regime, then the `ℓ¹`-mass of `f₁` is at least `(δ/4)·(2·dSup P N₀ N + 1)`. -/
theorem ss_mass_bound_of_manyShifts {P : Polynomial ℤ} {s N₀ N D : ℕ} {f₀ f₁ : ℤ → ℂ} {δ : ℝ}
    (hd : 2 ≤ P.natDegree) (hN : 1 ≤ N) (hN₀ : 1 ≤ N₀) (hD : 1 ≤ D)
    (hDN : (D : ℝ) ≤ (N : ℝ) ^ P.natDegree) (hgap : 2 * (N : ℝ) ^ P.natDegree < (N₀ : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hs0 : SupportIn f₀ N₀) (hs1 : SupportIn f₁ N₀)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1)
    (hmany : ManyShiftsHypδ P s N₀ N D f₀ f₁ δ) :
    δ / 4 * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) ≤ ∑' x : ℤ, ‖f₁ x‖ := by
  obtain ⟨H, hHmem, hHcard, hHlev⟩ := hmany
  have hd1 : 1 ≤ P.natDegree := by omega
  -- `2 N^d < N₀` forces `N ≤ N₀`
  have hNleN₀ : N ≤ N₀ := by
    have h1 : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ (by exact_mod_cast hN) (by omega)
    have h2 : (N : ℝ) < (N₀ : ℝ) := by linarith
    exact_mod_cast h2.le
  -- the shift set is nonempty, hence so is `H`
  have hQpos : 0 < (arithIcc P.leadingCoeff D).card := arithIcc_card_pos (P := P) hD
  have hQposR : (0 : ℝ) < ((arithIcc P.leadingCoeff D).card : ℝ) := by exact_mod_cast hQpos
  have hden : 0 < δ / 4 / (1 + (s : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)|) := by positivity
  have hHne : H.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    have h2 := hHcard
    rw [hc, Finset.card_empty] at h2
    have h3 : 0 < (δ / 4 / (1 + (s : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)|)) *
        ((arithIcc P.leadingCoeff D).card : ℝ) ^ (2 * (s - 2)) :=
      mul_pos hden (pow_pos hQposR _)
    linarith
  obtain ⟨sh, hsh⟩ := hHne
  have hlev := hHlev sh hsh
  -- the iterated difference
  set F : ℤ → ℂ := iterDelta (s - 2) sh (dualFn N P f₀ f₁) with hFdef
  have hbF : ∀ x : ℤ, ‖F x‖ ≤ 1 :=
    norm_iterDelta_le_one (s - 2) sh (dualFn N P f₀ f₁)
      (dualFn_norm_le_one N P (f₀ := f₀) (f₁ := f₁) hb0 hb1)
  have hsuppF : FinSuppZ F :=
    iterDelta_finsupp_bound (k := s - 2) sh
      (FinSuppZ.of_supportIn
        (Work.Peluse.Tools.dualFn_supportIn (N := N₀) (M := N) (by omega) P f₀ f₁ hs0 hs1
          hNleN₀))
  have hmass := boxNormPow_le_mass (t := 2) (by norm_num)
    (fun _ : Fin 2 => arithIcc P.leadingCoeff D) (symIcc (dSup P N₀ N)) F hbF hsuppF
  have hScard : ((symIcc (dSup P N₀ N)).card : ℝ) = 2 * ((dSup P N₀ N : ℕ) : ℝ) + 1 := by
    rw [symIcc, Int.card_Icc]
    have h : ((dSup P N₀ N : ℕ) : ℤ) + 1 - -(((dSup P N₀ N : ℕ)) : ℤ) =
        (((2 * dSup P N₀ N + 1 : ℕ)) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
    push_cast
    ring
  have hSpos : 0 < ((symIcc (dSup P N₀ N)).card : ℝ) := by rw [hScard]; positivity
  -- the box norm gives the mass of `F`
  have h1 : δ / 4 ≤ (∑' x : ℤ, ‖F x‖) * ((symIcc (dSup P N₀ N)).card : ℝ)⁻¹ :=
    le_trans hlev hmass
  have h2 : δ / 4 * ((symIcc (dSup P N₀ N)).card : ℝ) ≤ ∑' x : ℤ, ‖F x‖ := by
    have h := mul_le_mul_of_nonneg_right h1 hSpos.le
    rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hSpos), mul_one] at h
  -- and the mass of `F` is that of `f₁`
  have h3 : (∑' x : ℤ, ‖F x‖) ≤ ∑' x : ℤ, ‖f₁ x‖ := by
    have hsum : Summable (fun x : ℤ => ‖dualFn N P f₀ f₁ x‖) :=
      summable_norm_of_finSuppZ (FinSuppZ.of_supportIn
        (Work.Peluse.Tools.dualFn_supportIn (N := N₀) (M := N) (by omega) P f₀ f₁ hs0 hs1
          hNleN₀))
    calc (∑' x : ℤ, ‖F x‖) ≤ ∑' x : ℤ, ‖dualFn N P f₀ f₁ x‖ :=
          iterDelta_tsum_le (k := s - 2) sh (dualFn N P f₀ f₁)
            (dualFn_norm_le_one N P (f₀ := f₀) (f₁ := f₁) hb0 hb1) hsum
      _ ≤ ∑' x : ℤ, ‖f₁ x‖ := dualFn_tsum_le hN P f₀ f₁ hb0 (FinSuppZ.of_supportIn hs1)
  rw [hScard] at h2
  push_cast
  linarith [h2, h3]

end

end Work.Peluse.Ulower.SsA
