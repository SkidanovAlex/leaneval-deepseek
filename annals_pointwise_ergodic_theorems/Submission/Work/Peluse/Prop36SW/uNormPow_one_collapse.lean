import Mathlib
import Submission.Work.Peluse.TransferUp.boxNormPow_transfer_up
import Submission.Work.Peluse.Prop36SW.pairFormNatAbsLe
import Submission.Work.Peluse.Prop36SW.windowLagPairForm

/-!
# Collapsing the `U¹` norm of a window function from the step set `[L]` down to `[2M+1]`

`Work.Peluse.uNormPow 1 (arithIcc 1 L) (symIcc M) f` is the `2`-nd (first) Gowers box-norm power of
`f` over the single step set `[L] = {1, …, L}` and the window `symIcc M = [-M, M]`.  For a function
supported in `[-M, M]` and any `L ≥ 2M+1` the long step set is *at worst diluted*: the norm at `[L]`
is bounded by an absolute constant times the dilution factor `(2M+1)/L` times the norm at the
shortest admissible step set `[2M+1]`, i.e. the support diameter.

The proof is the exact computation of the `ℓ²`-mass of the window sums.  Put `H = 2M+1`,
`Σ = ∑_{y ∈ [-M,M]} f y` and

`PF = ∑_{y,k ∈ [-M,M]} |y-k| · Re (f y · conj (f k))`

and, for `K ≥ 1`, `T_K = ∑_x ‖∑_{y ∈ [1,K]} f (x+y)‖²`.  Because `f` is supported in `[-M,M]`,

`T_K = ∑_{y,k} f y conj (f k) · #{(h,h') ∈ [1,K]² : h' - h = k - y}
     = K ‖Σ‖² − PF`   (`|k-y| ≤ 2M < K` for every pair with `f y conj (f k) ≠ 0`),

which is `windowLagPairForm`.  The pair form itself satisfies the sharp bound `PF ≤ M‖Σ‖²`
(`pairFormNatAbsLe`, equality at `f = δ_{-M} + δ_M`), so `T_H ≥ (M+1)‖Σ‖²` and therefore

`T_L = T_H + (L−H)‖Σ‖² ≤ T_H (1 + (L−H)/(M+1)) ≤ 2 (L/H) T_H`   (`H = 2M+1`, `L ≥ H`).

Finally `uNormPow 1 [K] ([-M,M]) f = |symIcc M|⁻¹ K⁻² T_K`, so the two `K⁻²` and `|symIcc M|⁻¹`
factors produce exactly the stated `2 · (H/L)` gain.
-/

open scoped BigOperators

namespace Work.Peluse.Prop36SW

/-- Peluse's first box-norm power at the step set `arithIcc 1 K` and the window `symIcc M` is the
`ℓ²`-mass of the `K`-window sums, normalised by `|symIcc M| · K²`
(`Work.Peluse.Track.boxNormPow_one_arithIcc_window`, here with `d = 1`). -/
private lemma uNormPow_one_eq_windowSum (M K : ℕ) (hK : 1 ≤ K) (f : ℤ → ℂ)
    (hsup : Work.Peluse.SupportIn f M) :
    Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) K) (Work.Peluse.symIcc M) f
      = ((Work.Peluse.symIcc M).card : ℝ)⁻¹ * ((K : ℝ))⁻¹ ^ 2
          * ∑ x ∈ Work.Peluse.symIcc (M + K), ‖∑ y ∈ Finset.Icc 1 K, f (x + (y : ℤ))‖ ^ 2 := by
  have h := Work.Peluse.Track.boxNormPow_one_arithIcc_window (d := 1) (H := K) (N := M)
      (by norm_num) hK f hsup
  simpa [Work.Peluse.uNormPow, Int.natAbs_one, mul_one] using h

theorem uNormPow_one_collapse :
    ∃ C : ℝ, 0 < C ∧ ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ M → 2 * M + 1 ≤ L →
      Work.Peluse.SupportIn f M → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M) f
          ≤ C * ((((2 * M + 1 : ℕ) : ℝ)) / (L : ℝ))
              * Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1)) (Work.Peluse.symIcc M) f := by
  refine ⟨2, by norm_num, ?_⟩
  intro L M f hM hLM hsup hb
  -- the two window-sum identities for `uNormPow 1`
  have hwinL := uNormPow_one_eq_windowSum M L (by omega) f hsup
  have hwinH := uNormPow_one_eq_windowSum M (2 * M + 1) (by omega) f hsup
  -- the two lag identities `T_K = K ‖Σ‖² - PF`
  have hTL := windowLagPairForm (M := M) (K := L) hsup hLM
  have hTH := windowLagPairForm (M := M) (K := 2 * M + 1) hsup (le_refl _)
  -- the sharp pair-form bound `PF ≤ M ‖Σ‖²`
  have hP := pairFormNatAbsLe (M := M) (f := f) hsup
  -- ## notation
  set A : ℝ := ‖∑ y ∈ Work.Peluse.symIcc M, f y‖ ^ 2 with hA
  set PF : ℝ := ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
            (((y - k).natAbs : ℝ)) * (f y * star (f k)).re with hPF
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hP' : PF ≤ (M : ℝ) * A := by rw [hPF, hA]; exact hP
  have hHcast : (((2 * M + 1 : ℕ)) : ℝ) = 2 * (M : ℝ) + 1 := by push_cast; ring
  have hHL : ((2 * M + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLM
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
  -- ## the key real inequality `PF · (2L - H) ≤ L·H·A`
  have hkey : PF * (2 * (L : ℝ) - ((2 * M + 1 : ℕ) : ℝ)) ≤ ((L : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) * A := by
    have h2 : 0 ≤ 2 * (L : ℝ) - ((2 * M + 1 : ℕ) : ℝ) := by
      have : ((2 * M + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by linarith
      linarith
    have h1 : PF * (2 * (L : ℝ) - ((2 * M + 1 : ℕ) : ℝ))
        ≤ ((M : ℝ) * A) * (2 * (L : ℝ) - ((2 * M + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hP' h2
    have h3 : (M : ℝ) * (2 * (L : ℝ) - ((2 * M + 1 : ℕ) : ℝ)) ≤ (L : ℝ) * ((2 * M + 1 : ℕ) : ℝ) := by
      rw [hHcast]; nlinarith [hHL, hMnn, hM]
    have h4 : ((M : ℝ) * A) * (2 * (L : ℝ) - ((2 * M + 1 : ℕ) : ℝ))
        ≤ ((L : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) * A := by
      have := mul_le_mul_of_nonneg_right h3 hAnn
      linarith [this]
    linarith
  -- ## `T_L · H ≤ 2L · T_H`
  have hTL' : (∑ x ∈ Work.Peluse.symIcc (M + L), ‖∑ y ∈ Finset.Icc 1 L, f (x + (y : ℤ))‖ ^ 2)
      = (L : ℝ) * A - PF := by rw [hTL, hA, hPF]
  have hTH' : (∑ x ∈ Work.Peluse.symIcc (M + (2 * M + 1)),
              ‖∑ y ∈ Finset.Icc 1 (2 * M + 1), f (x + (y : ℤ))‖ ^ 2)
      = ((2 * M + 1 : ℕ) : ℝ) * A - PF := by rw [hTH, hA, hPF]
  have hbound : (∑ x ∈ Work.Peluse.symIcc (M + L), ‖∑ y ∈ Finset.Icc 1 L, f (x + (y : ℤ))‖ ^ 2)
        * ((2 * M + 1 : ℕ) : ℝ)
      ≤ 2 * (L : ℝ) * (∑ x ∈ Work.Peluse.symIcc (M + (2 * M + 1)),
              ‖∑ y ∈ Finset.Icc 1 (2 * M + 1), f (x + (y : ℤ))‖ ^ 2) := by
    rw [hTL', hTH']
    nlinarith [hkey]
  -- ## the final division bookkeeping
  set TL : ℝ := ∑ x ∈ Work.Peluse.symIcc (M + L), ‖∑ y ∈ Finset.Icc 1 L, f (x + (y : ℤ))‖ ^ 2 with hTLD
  set TH : ℝ := ∑ x ∈ Work.Peluse.symIcc (M + (2 * M + 1)),
      ‖∑ y ∈ Finset.Icc 1 (2 * M + 1), f (x + (y : ℤ))‖ ^ 2 with hTHD
  set H : ℝ := ((2 * M + 1 : ℕ) : ℝ) with hH
  set Sm : ℝ := ((Work.Peluse.symIcc M).card : ℝ) with hSm
  have hHpos : 0 < H := by rw [hH]; positivity
  have hSpos : 0 < Sm := by
    rw [hSm]
    have hcard : 0 < (Work.Peluse.symIcc M).card :=
      Finset.card_pos.mpr ⟨0, by simp [Work.Peluse.symIcc]⟩
    exact_mod_cast hcard
  have hbound' : TL * H ≤ 2 * (L : ℝ) * TH := by rw [hTLD, hTHD, hH]; exact hbound
  have hTLle : TL ≤ 2 * (L : ℝ) * TH / H := by
    rw [le_div_iff₀ hHpos]; linarith [hbound']
  calc Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M) f
      = Sm⁻¹ * ((L : ℝ))⁻¹ ^ 2 * TL := by rw [hwinL, hTLD, hSm]
    _ ≤ Sm⁻¹ * ((L : ℝ))⁻¹ ^ 2 * (2 * (L : ℝ) * TH / H) := by
        apply mul_le_mul_of_nonneg_left hTLle; positivity
    _ = 2 * (H / (L : ℝ)) * (Sm⁻¹ * H⁻¹ ^ 2 * TH) := by
        field_simp
    _ = 2 * (H / (L : ℝ))
          * Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1)) (Work.Peluse.symIcc M) f := by
        rw [hwinH, hTHD, hSm, hH]

end Work.Peluse.Prop36SW
