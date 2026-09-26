import Mathlib
import Submission.Work.Asymptotics.Tile.tileLayerDefs
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Gcusp_tile_bound
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.Tile.tileSharpTail

/-!
# The polynomial window on the cusp-`±1` tiles

This module supplies `Work.Asymptotics.Tile.tileWin` (the statement
`Work.Asymptotics.TileWin`, defined in `Submission/Work/Asymptotics/Tile/tileLayerDefs.lean`).

## The target, and how it is split here

`Work.Asymptotics.TileWin ℓ d` states: on the cusp-`±1` tiles `τ = n +ᵥ w` (`w ∈ E = KEpsilon`,
`n = ±1`) and for `1 ≤ t ≤ scale w` the kernel differs from its cusp model by a polynomial:

  `‖Kaxis (Kfun ℓ d) (n +ᵥ w) t − Aexp (Gcusp ℓ d) (n +ᵥ w) t‖ ≤ C (scale w)^N t^M`.

The kernel `Kaxis (Kfun ℓ d) (n+ᵥw) t` is *not* polynomially bounded in `scale w` along the tile
(for `d = 24`; numerically confirmed: at `w = i/(2k)`, `t = 2k−1` it is `Θ(e^{2πt}(2k)^{12})`), so
the content of the target is the **cancellation** between the kernel and its cusp model.  The two
proved halves of that cancellation used here are:

* `Work.Asymptotics.Tile.tileSharpTail` (proved): for `t ≥ 2 Im (S•w) + 1` the deviation is
  `O((scale w)^N t^M e^{−π(t − Im(S•w))})` — the region above every pole of `z ↦ K(τ,z)`, whose
  orbit points of height `≥ 1` are exactly the `S•w + k` (all of height `Im(S•w)`),
  see `tileSharpTail`'s module docs;
* `Work.Asymptotics.Tile.TileBelowPoleWindow` (**stated here, the reduction below proves that it
  together with `tileSharpTail` implies the target**): the same bound on the complementary range
  `1 ≤ t ≤ 2 Im (S•w) + 1`.

The second half is the genuinely non-trivial one (the "below-pole window"); the reduction
`tileWin_of_belowPole` is the whole content of this module's proof of `tileWin`.
-/

set_option maxHeartbeats 1600000

namespace Work.Asymptotics.Tile

open UpperHalfPlane
open Work.Asymptotics.EtailE (Bdd)

/-- `j` is `T`-invariant, so its tile translate obeys the `Bdd (2π)` bound. -/
lemma Bdd.vadd_j (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd (2 * Real.pi) (fun w : ℍ => Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)) :=
  Bdd.shift (F := fun w : ℍ => Work.Kernels.jInvariantFun w) EtailE.E_bdd_j
    (fun τ => Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ) n hn

/-- `Δ` is `T`-invariant, so `Δ^{-1}` on the tile obeys the `Bdd (2π)` bound. -/
lemma Bdd.vadd_invDelta (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd (2 * Real.pi) (fun w : ℍ => (Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w))⁻¹) :=
  Bdd.shift (F := fun w : ℍ => (Work.Kernels.DeltaFun w)⁻¹) EtailE.E_bdd_invDelta
    (fun τ => by rw [Work.Kernels.KernelFacts.DeltaFun_vadd_one]) n hn

/-- `fk 2 = E₁₄/Δ` on the tile. -/
lemma Bdd.vadd_fk_two (ℓ : Work.Kernels.LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd (2 * Real.pi) (fun w : ℍ => Work.Kernels.E14Fun ((n : ℝ) +ᵥ w)
      / Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)) :=
  Bdd.shift (F := fun w : ℍ => Work.Kernels.E14Fun w / Work.Kernels.DeltaFun w)
    (EtailE.E_bdd_E14_div_Delta ℓ)
    (fun τ => by
      show Work.Kernels.E14Fun ((1 : ℝ) +ᵥ τ) / Work.Kernels.DeltaFun ((1 : ℝ) +ᵥ τ)
        = Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ
      rw [Work.Kernels.KernelFacts.E14Fun_vadd_one,
        Work.Kernels.KernelFacts.DeltaFun_vadd_one]) n hn

/-- `fk (-2) = E₁₀/Δ` on the tile. -/
lemma Bdd.vadd_fk_neg_two (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd (2 * Real.pi) (fun w : ℍ => Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)
      / Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)) :=
  Bdd.shift (F := fun w : ℍ => Work.Kernels.E10Fun w / Work.Kernels.DeltaFun w)
    EtailE.E_bdd_E10_div_Delta
    (fun τ => by
      show Work.Kernels.E10Fun ((1 : ℝ) +ᵥ τ) / Work.Kernels.DeltaFun ((1 : ℝ) +ᵥ τ)
        = Work.Kernels.E10Fun τ / Work.Kernels.DeltaFun τ
      rw [Work.Kernels.KernelFacts.E10Fun_vadd_one,
        Work.Kernels.KernelFacts.DeltaFun_vadd_one]) n hn

end Work.Asymptotics.Tile

set_option maxHeartbeats 1600000

namespace Work.Asymptotics.Tile

/-- **The below-pole window on the cusp-`±1` tiles.**  For `w ∈ E = KEpsilon`, `n = ±1` and
`1 ≤ t ≤ 2 Im (S • w) + 1` the kernel `Kaxis (Kfun ℓ d) (n +ᵥ w)` differs from its cusp model
`Aexp (Gcusp ℓ d) (n +ᵥ w)` by `O((scale w)^N t^M)`.

The upper end `2 Im (S • w) + 1` is the correct "above every pole" threshold: all orbit points of
`z ↦ K(n +ᵥ w, z)` of height `≥ 1` are the translates `S • w + k` (`k ∈ ℤ`), all at the *same*
height `Im (S • w)`, and `tileSharpTail` handles `t ≥ 2 Im (S • w) + 1`.  (The sharp threshold
`Im (S • w) + 1` is what `Work.Asymptotics.Tile.Kdev_funnel_far` and the sharp strip deviations
produce; the factor `2` here is the crude one that the `TB`-calculus of `tileTB` uses.) -/
def TileBelowPoleWindow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ,
      (n = 1 ∨ n = -1) → ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M

/-- **The far regime of the tile deviation**: `1 ≤ t ≤ Im (S•w) − 1`.  Here the contour point
`i t` stays at distance `≥ 1` from every pole `S•w + k` of `z ↦ K(n +ᵥ w, z)`, and the divisor
`Δ(i t)·(j(n+ᵥw) − j(i t))` is bounded below by a positive constant: indeed
`|Δ(i t) j(n+ᵥw)| ≍ e^{2π(Im(S•w) − t)} ≥ e^{2π}` while `E₄(i t)³ ≈ 1`. -/
def TileBelowPoleFar (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ,
      (n = 1 ∨ n = -1) → ∀ t : ℝ, 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M

/-- **The resonant strip of the tile deviation**: `|t − Im (S•w)| ≤ 1`.  This is the only range
in which the divisor `Δ(i t)(j(n+ᵥw) − j(i t)) = Δ(i t)j(n+ᵥw) − E₄(i t)³` can be small: both of
its two terms are of size `≍ 1` here, and they cancel exactly at the *coincidences* `j(i t) = j(τ)`
— which, since every orbit point of `τ = n +ᵥ w` of height `≥ 1` is a translate `S•w + k`, happen
only at `t = Im (S•w)` and only when `Re (S•w) ∈ ℤ`, i.e. when `w` lies on the boundary circles
`|w ∓ 1/2| = 1/2` of `𝒟` (so for `w ∈ E ⊆ 𝒟` open they happen only in the limit — but the
divisor is *small* there, and the numerator `KfunClear` vanishes proportionally, which is what
makes the strip estimate the crux of the target). -/
def TileBelowPoleStrip (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ,
      (n = 1 ∨ n = -1) → ∀ t : ℝ, (ModularGroup.S • w).im - 1 ≤ t →
        t ≤ (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M

/-- **The above-pole regime of the tile window**: `Im (S•w) + 1 ≤ t ≤ 2 Im (S•w) + 1`.  Here the
divisor is again bounded below by a positive constant, with the roles of the two terms reversed:
`|Δ(i t)j(n+ᵥw)| ≍ e^{2π(Im(S•w) − t)} ≤ e^{−2π}` is now *small* while `|E₄(i t)³| ≥ 1/2`. -/
def TileBelowPoleTop (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ,
      (n = 1 ∨ n = -1) → ∀ t : ℝ, (ModularGroup.S • w).im + 1 ≤ t →
        t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M

/-- If a bound already holds with exponents `(C, N, M)` it holds with any larger exponents, as
soon as `s, t ≥ 1`. -/
lemma le_mul_rpow_mono {s t C N M C' N' M' : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hN' : N ≤ N') (hM' : M ≤ M') (hC' : C ≤ C') (hC0 : 0 ≤ C) :
    C * s ^ N * t ^ M ≤ C' * s ^ N' * t ^ M' := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : s ^ N ≤ s ^ N' := Real.rpow_le_rpow_of_exponent_le hs hN'
  have h2 : t ^ M ≤ t ^ M' := Real.rpow_le_rpow_of_exponent_le ht hM'
  have h3 : s ^ N * t ^ M ≤ s ^ N' * t ^ M' :=
    mul_le_mul h1 h2 (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hs0.le _)
  have h3nn : (0 : ℝ) ≤ s ^ N * t ^ M :=
    mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg ht0.le _)
  have hC'0 : (0 : ℝ) ≤ C' := le_trans hC0 hC'
  calc C * s ^ N * t ^ M = C * (s ^ N * t ^ M) := by ring
    _ ≤ C' * (s ^ N' * t ^ M') := mul_le_mul hC' h3 h3nn hC'0
    _ = C' * s ^ N' * t ^ M' := by ring

/-- **The three regimes of the below-pole window cover it.** -/
theorem tileBelowPoleWindow_of_pieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hF : TileBelowPoleFar ℓ d) (hS : TileBelowPoleStrip ℓ d) (hT : TileBelowPoleTop ℓ d) :
    TileBelowPoleWindow ℓ d := by
  obtain ⟨CF, NF, MF, hCF, hNF, hMF, bF⟩ := hF
  obtain ⟨CS, NS, MS, hCS, hNS, hMS, bS⟩ := hS
  obtain ⟨CT, NT, MT, hCT, hNT, hMT, bT⟩ := hT
  refine ⟨max (max CF CS) CT + 1, max (max NF NS) NT, max (max MF MS) MT, by positivity,
    le_trans hNF (le_trans (le_max_left NF NS) (le_max_left (max NF NS) NT)),
    le_trans hMF (le_trans (le_max_left MF MS) (le_max_left (max MF MS) MT)), ?_⟩
  intro w hw n hn t ht1 ht2
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  by_cases h1 : t < (ModularGroup.S • w).im - 1
  · refine le_trans (bF w hw n hn t ht1 (le_of_lt h1)) ?_
    exact le_mul_rpow_mono hs1 ht1
      (le_trans (le_max_left NF NS) (le_max_left (max NF NS) NT))
      (le_trans (le_max_left MF MS) (le_max_left (max MF MS) MT))
      (by linarith [le_max_left CF CS, le_max_left (max CF CS) CT]) hCF.le
  · push_neg at h1
    by_cases h2 : t < (ModularGroup.S • w).im + 1
    · refine le_trans (bS w hw n hn t h1 (le_of_lt h2)) ?_
      exact le_mul_rpow_mono hs1 ht1
        (le_trans (le_max_right NF NS) (le_max_left (max NF NS) NT))
        (le_trans (le_max_right MF MS) (le_max_left (max MF MS) MT))
        (by linarith [le_max_right CF CS, le_max_left (max CF CS) CT]) hCS.le
    · push_neg at h2
      refine le_trans (bT w hw n hn t h2 ht2) ?_
      exact le_mul_rpow_mono hs1 ht1 (le_max_right (max NF NS) NT)
        (le_max_right (max MF MS) MT) (by linarith [le_max_right (max CF CS) CT]) hCT.le

/-- **The reduction of the tile window to its two regimes.**

The ranges `[1, 2 Im (S•w) + 1]` and `[2 Im (S•w) + 1, ∞)` cover `[1, scale w]`, because
`Im (S • w) ≥ 0`; on the second range `tileSharpTail`'s exponential factor is `≤ 1` thanks to
`Im (S • w) ≥ 2`. -/
theorem tileWin_of_belowPole (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hW : TileBelowPoleWindow ℓ d) : Work.Asymptotics.TileWin ℓ d := by
  obtain ⟨Cw, Nw, Mw, hCw, hNw, hMw, hWb⟩ := hW
  obtain ⟨Cs, Ns, Ms, hCs, hNs, hMs, hSb⟩ := tileSharpTail ℓ d hd
  refine ⟨max Cw Cs + 1, max Nw Ns, max Mw Ms, by positivity, le_max_of_le_left hNw,
    le_max_of_le_left hMw, ?_⟩
  intro w hw n hn t ht1 htle
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hA2 : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have hpN1 : (Work.Kernels.scale w) ^ Nw ≤ (Work.Kernels.scale w) ^ (max Nw Ns) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hpN2 : (Work.Kernels.scale w) ^ Ns ≤ (Work.Kernels.scale w) ^ (max Nw Ns) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have htM1 : t ^ Mw ≤ t ^ (max Mw Ms) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  have htM2 : t ^ Ms ≤ t ^ (max Mw Ms) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right _ _)
  have hbound1 : Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw
      ≤ (max Cw Cs + 1) * (Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms) := by
    have h2 : (Work.Kernels.scale w) ^ Nw * t ^ Mw
        ≤ (Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms) :=
      mul_le_mul hpN1 htM1 (Real.rpow_nonneg (le_trans zero_le_one ht1) _)
        (Real.rpow_nonneg hs0.le _)
    calc Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw
        = Cw * ((Work.Kernels.scale w) ^ Nw * t ^ Mw) := by ring
      _ ≤ Cw * ((Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms)) :=
          mul_le_mul_of_nonneg_left h2 hCw.le
      _ ≤ (max Cw Cs + 1) * ((Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [le_max_left Cw Cs]
      _ = (max Cw Cs + 1) * (Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms) := by ring
  have hbound2 : ∀ (hAt : (ModularGroup.S • w).im ≤ t),
      Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms
        * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
      ≤ (max Cw Cs + 1) * (Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms) := by
    intro hAt
    have hexp : Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h0 : (0 : ℝ) ≤ t - (ModularGroup.S • w).im := by linarith
      nlinarith [Real.pi_pos, h0]
    have h2 : (Work.Kernels.scale w) ^ Ns * t ^ Ms
        ≤ (Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms) :=
      mul_le_mul hpN2 htM2 (Real.rpow_nonneg (le_trans zero_le_one ht1) _)
        (Real.rpow_nonneg hs0.le _)
    calc Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
        ≤ Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms * 1 := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
      _ = Cs * ((Work.Kernels.scale w) ^ Ns * t ^ Ms) := by ring
      _ ≤ (max Cw Cs + 1) * ((Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms)) := by
          refine le_trans (mul_le_mul_of_nonneg_left h2 hCs.le) ?_
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [le_max_right Cw Cs]
      _ = (max Cw Cs + 1) * (Work.Kernels.scale w) ^ (max Nw Ns) * t ^ (max Mw Ms) := by ring
  by_cases hcase : t ≤ 2 * (ModularGroup.S • w).im + 1
  · exact le_trans (hWb w hw n hn t ht1 hcase) hbound1
  · have hge : 2 * (ModularGroup.S • w).im + 1 ≤ t := le_of_lt (lt_of_not_ge hcase)
    exact le_trans (hSb w n hn hw t hge) (hbound2 (by linarith))

end Work.Asymptotics.Tile
